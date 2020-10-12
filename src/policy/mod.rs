// Miniscript
// Written in 2018 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//!  Script Policies
//!
//! Tools for representing Bitcoin scriptpubkeys as abstract spending policies.
//! These may be compiled to Miniscript, which contains extra information to
//! describe the exact representation as Bitcoin script.
//!
//! The format represents EC public keys abstractly to allow wallets to replace
//! these with BIP32 paths, pay-to-contract instructions, etc.
//!

#[cfg(feature = "compiler")]
pub mod compiler;
pub mod concrete;
pub mod semantic;

use descriptor::Descriptor;
use miniscript::{Miniscript, ScriptContext};
use Terminal;

pub use self::concrete::Policy as Concrete;
/// Semantic policies are "abstract" policies elsewhere; but we
/// avoid this word because it is a reserved keyword in Rust
pub use self::semantic::Policy as Semantic;
use Error;
use MiniscriptKey;

/// Policy entailment algorithm maximum number of terminals allowed
const ENTAILMENT_MAX_TERMINALS: usize = 20;
/// Trait describing script representations which can be lifted into
/// an abstract policy, by discarding information.
/// After Lifting all policies are converted into `KeyHash(Pk::HasH)` to
/// maintain the following invariant:
/// `Lift(Concrete) == Concrete -> Miniscript -> Script -> Miniscript -> Semantic`
pub trait Liftable<Pk: MiniscriptKey> {
    /// Convert the object into an abstract policy
    fn lift(&self) -> Result<Semantic<Pk>, Error>;
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Liftable<Pk> for Miniscript<Pk, Ctx> {
    fn lift(&self) -> Result<Semantic<Pk>, Error> {
        // check whether the root miniscript can have a spending path that is
        // a combination of heightlock and timelock
        if self.ext.timelock_info.contains_unspendable_path() {
            return Err(Error::PolicyError(
                concrete::PolicyError::HeightTimeLockCombination,
            ));
        }
        self.as_inner().lift()
    }
}

impl<Pk: MiniscriptKey, Ctx: ScriptContext> Liftable<Pk> for Terminal<Pk, Ctx> {
    fn lift(&self) -> Result<Semantic<Pk>, Error> {
        let ret = match *self {
            Terminal::PkK(ref pk) => Semantic::KeyHash(pk.to_pubkeyhash()),
            Terminal::PkH(ref pkh) => Semantic::KeyHash(pkh.clone()),
            Terminal::After(t) => Semantic::After(t),
            Terminal::Older(t) => Semantic::Older(t),
            Terminal::Sha256(h) => Semantic::Sha256(h),
            Terminal::Hash256(h) => Semantic::Hash256(h),
            Terminal::Ripemd160(h) => Semantic::Ripemd160(h),
            Terminal::Hash160(h) => Semantic::Hash160(h),
            Terminal::True => Semantic::Trivial,
            Terminal::False => Semantic::Unsatisfiable,
            Terminal::Alt(ref sub)
            | Terminal::Swap(ref sub)
            | Terminal::Check(ref sub)
            | Terminal::DupIf(ref sub)
            | Terminal::Verify(ref sub)
            | Terminal::NonZero(ref sub)
            | Terminal::ZeroNotEqual(ref sub) => sub.node.lift()?,
            Terminal::AndV(ref left, ref right) | Terminal::AndB(ref left, ref right) => {
                Semantic::Threshold(2, vec![left.node.lift()?, right.node.lift()?])
            }
            Terminal::AndOr(ref a, ref b, ref c) => Semantic::Threshold(
                1,
                vec![
                    Semantic::Threshold(2, vec![a.node.lift()?, c.node.lift()?]),
                    b.node.lift()?,
                ],
            ),
            Terminal::OrB(ref left, ref right)
            | Terminal::OrD(ref left, ref right)
            | Terminal::OrC(ref left, ref right)
            | Terminal::OrI(ref left, ref right) => {
                Semantic::Threshold(1, vec![left.node.lift()?, right.node.lift()?])
            }
            Terminal::Thresh(k, ref subs) => {
                let semantic_subs: Result<_, Error> =
                    subs.into_iter().map(|s| s.node.lift()).collect();
                Semantic::Threshold(k, semantic_subs?)
            }
            Terminal::Multi(k, ref keys) => Semantic::Threshold(
                k,
                keys.into_iter()
                    .map(|k| Semantic::KeyHash(k.to_pubkeyhash()))
                    .collect(),
            ),
        }
        .normalized();
        Ok(ret)
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Descriptor<Pk> {
    fn lift(&self) -> Result<Semantic<Pk>, Error> {
        Ok(match *self {
            Descriptor::Bare(ref d) | Descriptor::Sh(ref d) => d.node.lift()?,
            Descriptor::Wsh(ref d) | Descriptor::ShWsh(ref d) => d.node.lift()?,
            Descriptor::Pk(ref p)
            | Descriptor::Pkh(ref p)
            | Descriptor::Wpkh(ref p)
            | Descriptor::ShWpkh(ref p) => Semantic::KeyHash(p.to_pubkeyhash()),
            Descriptor::Cov(ref _cov) => {
                unimplemented!("Semantic analysis not supported for covenants yet!")
            }
        })
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Semantic<Pk> {
    fn lift(&self) -> Result<Semantic<Pk>, Error> {
        Ok(self.clone())
    }
}

impl<Pk: MiniscriptKey> Liftable<Pk> for Concrete<Pk> {
    fn lift(&self) -> Result<Semantic<Pk>, Error> {
        // do not lift if there is a possible satisfaction
        // involving combination of timelocks and heightlocks
        self.check_timelocks()?;
        let ret = match *self {
            Concrete::Unsatisfiable => Semantic::Unsatisfiable,
            Concrete::Trivial => Semantic::Trivial,
            Concrete::Key(ref pk) => Semantic::KeyHash(pk.to_pubkeyhash()),
            Concrete::After(t) => Semantic::After(t),
            Concrete::Older(t) => Semantic::Older(t),
            Concrete::Sha256(h) => Semantic::Sha256(h),
            Concrete::Hash256(h) => Semantic::Hash256(h),
            Concrete::Ripemd160(h) => Semantic::Ripemd160(h),
            Concrete::Hash160(h) => Semantic::Hash160(h),
            Concrete::And(ref subs) => {
                let semantic_subs: Result<_, Error> = subs.iter().map(Liftable::lift).collect();
                Semantic::Threshold(2, semantic_subs?)
            }
            Concrete::Or(ref subs) => {
                let semantic_subs: Result<_, Error> =
                    subs.iter().map(|&(ref _p, ref sub)| sub.lift()).collect();
                Semantic::Threshold(1, semantic_subs?)
            }
            Concrete::Threshold(k, ref subs) => {
                let semantic_subs: Result<_, Error> = subs.iter().map(Liftable::lift).collect();
                Semantic::Threshold(k, semantic_subs?)
            }
        }
        .normalized();
        Ok(ret)
    }
}

#[cfg(test)]
mod tests {
    use super::{Concrete, Semantic};
    use std::str::FromStr;
    use DummyKey;

    type ConcretePol = Concrete<DummyKey>;
    type SemanticPol = Semantic<DummyKey>;

    fn concrete_policy_rtt(s: &str) {
        let conc = ConcretePol::from_str(s).unwrap();
        let output = conc.to_string();
        assert_eq!(s.to_lowercase(), output.to_lowercase());
    }

    fn semantic_policy_rtt(s: &str) {
        let sem = SemanticPol::from_str(s).unwrap();
        let output = sem.normalized().to_string();
        assert_eq!(s.to_lowercase(), output.to_lowercase());
    }

    #[test]
    fn test_timelock_validity() {
        // only height
        assert!(ConcretePol::from_str("after(100)").is_ok());
        // only time
        assert!(ConcretePol::from_str("after(1000000000)").is_ok());
        // disjunction
        assert!(ConcretePol::from_str("or(after(1000000000),after(100))").is_ok());
        // conjunction
        assert!(ConcretePol::from_str("and(after(1000000000),after(100))").is_err());
        // thresh with k = 1
        assert!(ConcretePol::from_str("thresh(1,pk(),after(1000000000),after(100))").is_ok());
        // thresh with k = 2
        assert!(ConcretePol::from_str("thresh(2,after(1000000000),after(100),pk())").is_err());
    }
    #[test]
    fn policy_rtt_tests() {
        concrete_policy_rtt("pk()");
        concrete_policy_rtt("or(1@pk(),1@pk())");
        concrete_policy_rtt("or(99@pk(),1@pk())");
        concrete_policy_rtt("and(pk(),or(99@pk(),1@older(12960)))");

        semantic_policy_rtt("pkh()");
        semantic_policy_rtt("or(pkh(),pkh())");
        semantic_policy_rtt("and(pkh(),pkh())");

        //fuzzer crashes
        assert!(ConcretePol::from_str("thresh()").is_err());
        assert!(SemanticPol::from_str("thresh(0)").is_err());
        assert!(SemanticPol::from_str("thresh()").is_err());
        concrete_policy_rtt("ripemd160(aaaaaaaaaaaaaaaaaaaaaa0Daaaaaaaaaabaaaaa)");
    }

    #[test]
    fn compile_invalid() {
        // Since the root Error does not support Eq type, we hvae to
        // compare the string representations of the error
        assert_eq!(
            ConcretePol::from_str("thresh(2,pk(),thresh(0))")
                .unwrap_err()
                .to_string(),
            "Threshold k must be greater than 0 and less than or equal to n 0<k<=n"
        );
        assert_eq!(
            ConcretePol::from_str("thresh(2,pk(),thresh(0,pk()))")
                .unwrap_err()
                .to_string(),
            "Threshold k must be greater than 0 and less than or equal to n 0<k<=n"
        );
        assert_eq!(
            ConcretePol::from_str("and(pk())").unwrap_err().to_string(),
            "And policy fragment must take 2 arguments"
        );
        assert_eq!(
            ConcretePol::from_str("or(pk())").unwrap_err().to_string(),
            "Or policy fragment must take 2 arguments"
        );
        assert_eq!(
            ConcretePol::from_str("thresh(3,after(0),pk(),pk())")
                .unwrap_err()
                .to_string(),
            "Time must be greater than 0; n > 0"
        );

        assert_eq!(
            ConcretePol::from_str("thresh(2,older(2147483650),pk(),pk())")
                .unwrap_err()
                .to_string(),
            "Relative/Absolute time must be less than 2^31; n < 2^31"
        );
    }

    //https://github.com/apoelstra/rust-miniscript/issues/41
    #[test]
    fn heavy_nest() {
        let policy_string = "thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk(),thresh(1,pk(),pk(),pk()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))";
        ConcretePol::from_str(&policy_string).unwrap_err();
    }
}

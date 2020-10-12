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

//! # Output Descriptors
//!
//! Tools for representing Bitcoin output's scriptPubKeys as abstract spending
//! policies known as "output descriptors". These include a Miniscript which
//! describes the actual signing policy, as well as the blockchain format (P2SH,
//! Segwit v0, etc.)
//!
//! The format represents EC public keys abstractly to allow wallets to replace
//! these with BIP32 paths, pay-to-contract instructions, etc.
//!

use std::fmt;
use std::str::{self, FromStr};

use bitcoin;
use bitcoin::hashes::hash160;
use bitcoin::hashes::hex::FromHex;
use bitcoin::secp256k1;
use bitcoin::util::bip32;
use elements::Script;
use elements::{opcodes, script, AddressParams};

#[cfg(feature = "serde")]
use serde::{de, ser};

use expression;
use miniscript;
use miniscript::context::ScriptContextError;
use miniscript::{Legacy, Miniscript, Segwitv0};
use Error;
use MiniscriptKey;
use Satisfier;
use ToPublicKey;

mod covenants;

use self::covenants::{CovenantAddressCtx, CovenantCtx};
// mod create_descriptor;
// mod satisfied_constraints;

// pub use self::create_descriptor::from_txin_with_witness_stack;
// pub use self::satisfied_constraints::Error as InterpreterError;
// pub use self::satisfied_constraints::SatisfiedConstraint;
// pub use self::satisfied_constraints::SatisfiedConstraints;
// pub use self::satisfied_constraints::Stack;

/// Script descriptor
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Descriptor<Pk: MiniscriptKey> {
    /// A raw scriptpubkey (including pay-to-pubkey) under Legacy context
    Bare(Miniscript<Pk, Legacy>),
    /// Pay-to-Pubkey
    Pk(Pk),
    /// Pay-to-PubKey-Hash
    Pkh(Pk),
    /// Pay-to-Witness-PubKey-Hash
    Wpkh(Pk),
    /// Pay-to-Witness-PubKey-Hash inside P2SH
    ShWpkh(Pk),
    /// Pay-to-ScriptHash with Legacy context
    Sh(Miniscript<Pk, Legacy>),
    /// Pay-to-Witness-ScriptHash with Segwitv0 context
    Wsh(Miniscript<Pk, Segwitv0>),
    /// P2SH-P2WSH with Segwitv0 context
    ShWsh(Miniscript<Pk, Segwitv0>),
    /// Covenant Desciptor
    Cov(CovenantCtx<Pk>),
}

#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub enum DescriptorPublicKey {
    SinglePub(DescriptorSinglePub),
    XPub(DescriptorXPub),
}

#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct DescriptorSinglePub {
    pub origin: Option<(bip32::Fingerprint, bip32::DerivationPath)>,
    pub key: bitcoin::PublicKey,
}

#[derive(Debug, Eq, PartialEq, Clone, Ord, PartialOrd, Hash)]
pub struct DescriptorXPub {
    pub origin: Option<(bip32::Fingerprint, bip32::DerivationPath)>,
    pub xpub: bip32::ExtendedPubKey,
    pub derivation_path: bip32::DerivationPath,
    pub is_wildcard: bool,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct DescriptorKeyParseError(&'static str);

impl fmt::Display for DescriptorKeyParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl fmt::Display for DescriptorPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DescriptorPublicKey::SinglePub(ref pk) => {
                maybe_fmt_master_id(f, &pk.origin)?;
                pk.key.fmt(f)?;
                Ok(())
            }
            DescriptorPublicKey::XPub(ref xpub) => {
                maybe_fmt_master_id(f, &xpub.origin)?;
                xpub.xpub.fmt(f)?;
                fmt_derivation_path(f, &xpub.derivation_path)?;
                if xpub.is_wildcard {
                    write!(f, "/*")?;
                }
                Ok(())
            }
        }
    }
}

/// Writes the fingerprint of the origin, if there is one.
fn maybe_fmt_master_id(
    f: &mut fmt::Formatter,
    origin: &Option<(bip32::Fingerprint, bip32::DerivationPath)>,
) -> fmt::Result {
    if let Some((ref master_id, ref master_deriv)) = *origin {
        fmt::Formatter::write_str(f, "[")?;
        for byte in master_id.into_bytes().iter() {
            write!(f, "{:02x}", byte)?;
        }
        fmt_derivation_path(f, master_deriv)?;
        fmt::Formatter::write_str(f, "]")?;
    }

    Ok(())
}

/// Writes a derivation path to the formatter, no leading 'm'
fn fmt_derivation_path(f: &mut fmt::Formatter, path: &bip32::DerivationPath) -> fmt::Result {
    for child in path {
        write!(f, "/{}", child)?;
    }
    Ok(())
}

impl FromStr for DescriptorPublicKey {
    type Err = DescriptorKeyParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // A "raw" public key without any origin is the least we accept.
        if s.len() < 66 {
            return Err(DescriptorKeyParseError(
                "Key too short (<66 char), doesn't match any format",
            ));
        }

        for ch in s.as_bytes() {
            if *ch < 20 || *ch > 127 {
                return Err(DescriptorKeyParseError(
                    "Encountered an unprintable character",
                ));
            }
        }

        let mut parts = s[1..].split(']');

        // They may specify an origin
        let mut origin = None;
        if s.chars().next().unwrap() == '[' {
            let mut raw_origin = parts
                .next()
                .ok_or(DescriptorKeyParseError("Unclosed '['"))?
                .split('/');

            let origin_id_hex = raw_origin.next().ok_or(DescriptorKeyParseError(
                "No master fingerprint found after '['",
            ))?;

            if origin_id_hex.len() != 8 {
                return Err(DescriptorKeyParseError(
                    "Master fingerprint should be 8 characters long",
                ));
            }
            let parent_fingerprint = bip32::Fingerprint::from_hex(origin_id_hex).map_err(|_| {
                DescriptorKeyParseError("Malformed master fingerprint, expected 8 hex chars")
            })?;

            let origin_path = raw_origin
                .map(|p| bip32::ChildNumber::from_str(p))
                .collect::<Result<bip32::DerivationPath, bip32::Error>>()
                .map_err(|_| {
                    DescriptorKeyParseError("Error while parsing master derivation path")
                })?;
            origin = Some((parent_fingerprint, origin_path));
        }

        let key_part = if origin == None {
            Ok(s)
        } else {
            parts
                .next()
                .ok_or(DescriptorKeyParseError("No key after origin."))
        }?;

        // To support testnet as well
        if key_part.contains("pub") {
            let (xpub, derivation_path, is_wildcard) = Self::parse_xpub_deriv(key_part)?;

            Ok(DescriptorPublicKey::XPub(DescriptorXPub {
                origin,
                xpub,
                derivation_path,
                is_wildcard,
            }))
        } else {
            let key = bitcoin::PublicKey::from_str(key_part)
                .map_err(|_| DescriptorKeyParseError("Error while parsing simple public key"))?;
            Ok(DescriptorPublicKey::SinglePub(DescriptorSinglePub {
                key,
                origin,
            }))
        }
    }
}

impl DescriptorPublicKey {
    /// Parse an extended public key concatenated to a derivation path.
    fn parse_xpub_deriv(
        key_deriv: &str,
    ) -> Result<(bip32::ExtendedPubKey, bip32::DerivationPath, bool), DescriptorKeyParseError> {
        let mut key_deriv = key_deriv.split('/');
        let xpub_str = key_deriv.next().ok_or(DescriptorKeyParseError(
            "No key found after origin description",
        ))?;
        let xpub = bip32::ExtendedPubKey::from_str(xpub_str)
            .map_err(|_| DescriptorKeyParseError("Error while parsing xpub."))?;

        let mut is_wildcard = false;
        let derivation_path = key_deriv
            .filter_map(|p| {
                if !is_wildcard && p == "*" {
                    is_wildcard = true;
                    None
                } else if !is_wildcard && p == "*'" {
                    Some(Err(DescriptorKeyParseError(
                        "Hardened derivation is currently not supported.",
                    )))
                } else if is_wildcard {
                    Some(Err(DescriptorKeyParseError(
                        "'*' may only appear as last element in a derivation path.",
                    )))
                } else {
                    Some(bip32::ChildNumber::from_str(p).map_err(|_| {
                        DescriptorKeyParseError("Error while parsing key derivation path")
                    }))
                }
            })
            .collect::<Result<bip32::DerivationPath, _>>()?;

        if (&derivation_path).into_iter().all(|c| c.is_normal()) {
            Ok((xpub, derivation_path, is_wildcard))
        } else {
            Err(DescriptorKeyParseError(
                "Hardened derivation is currently not supported.",
            ))
        }
    }

    /// Derives the specified child key if self is a wildcard xpub. Otherwise returns self.
    ///
    /// Panics if given a hardened child number
    pub fn derive(self, child_number: bip32::ChildNumber) -> DescriptorPublicKey {
        debug_assert!(child_number.is_normal());

        match self {
            DescriptorPublicKey::SinglePub(_) => self,
            DescriptorPublicKey::XPub(xpub) => {
                if xpub.is_wildcard {
                    DescriptorPublicKey::XPub(DescriptorXPub {
                        origin: xpub.origin,
                        xpub: xpub.xpub,
                        derivation_path: xpub.derivation_path.into_child(child_number),
                        is_wildcard: false,
                    })
                } else {
                    DescriptorPublicKey::XPub(xpub)
                }
            }
        }
    }
}

impl MiniscriptKey for DescriptorPublicKey {
    // This allows us to be able to derive public keys even for PkH s
    type Hash = Self;

    fn to_pubkeyhash(&self) -> Self {
        self.clone()
    }
}

impl ToPublicKey for DescriptorPublicKey {
    fn to_public_key(&self) -> bitcoin::PublicKey {
        match *self {
            DescriptorPublicKey::SinglePub(ref spub) => spub.key.to_public_key(),
            DescriptorPublicKey::XPub(ref xpub) => {
                let ctx = secp256k1::Secp256k1::verification_only();
                xpub.xpub
                    .derive_pub(&ctx, &xpub.derivation_path)
                    .expect("Shouldn't fail, only normal derivations")
                    .public_key
            }
        }
    }

    fn hash_to_hash160(hash: &Self::Hash) -> hash160::Hash {
        hash.to_public_key().to_pubkeyhash()
    }
}

impl<Pk: MiniscriptKey> Descriptor<Pk> {
    /// Convert a descriptor using abstract keys to one using specific keys
    /// This will panic if translatefpk returns an uncompressed key when
    /// converting to a Segwit descriptor. To prevent this panic, ensure
    /// translatefpk returns an error in this case instead.
    pub fn translate_pk<Fpk, Fpkh, Q, E>(
        &self,
        mut translatefpk: Fpk,
        mut translatefpkh: Fpkh,
    ) -> Result<Descriptor<Q>, E>
    where
        Fpk: FnMut(&Pk) -> Result<Q, E>,
        Fpkh: FnMut(&Pk::Hash) -> Result<Q::Hash, E>,
        Q: MiniscriptKey,
    {
        match *self {
            Descriptor::Bare(ref ms) => Ok(Descriptor::Bare(
                ms.translate_pk(&mut translatefpk, &mut translatefpkh)?,
            )),
            Descriptor::Pk(ref pk) => translatefpk(pk).map(Descriptor::Pk),
            Descriptor::Pkh(ref pk) => translatefpk(pk).map(Descriptor::Pkh),
            Descriptor::Wpkh(ref pk) => {
                if pk.is_uncompressed() {
                    panic!("Uncompressed pubkeys are not allowed in segwit v0 scripts");
                }
                translatefpk(pk).map(Descriptor::Wpkh)
            }
            Descriptor::ShWpkh(ref pk) => {
                if pk.is_uncompressed() {
                    panic!("Uncompressed pubkeys are not allowed in segwit v0 scripts");
                }
                translatefpk(pk).map(Descriptor::ShWpkh)
            }
            Descriptor::Sh(ref ms) => Ok(Descriptor::Sh(
                ms.translate_pk(&mut translatefpk, &mut translatefpkh)?,
            )),
            Descriptor::Wsh(ref ms) => Ok(Descriptor::Wsh(
                ms.translate_pk(&mut translatefpk, &mut translatefpkh)?,
            )),
            Descriptor::ShWsh(ref ms) => Ok(Descriptor::ShWsh(
                ms.translate_pk(&mut translatefpk, &mut translatefpkh)?,
            )),
            Descriptor::Cov(ref cov) => Ok(Descriptor::Cov(CovenantCtx {
                spend_ctx: None, //FIXME later if required
                commit_ctx: CovenantAddressCtx {
                    cov_info: cov.commit_ctx.cov_info.clone(),
                    redeem_pk: translatefpk(&cov.commit_ctx.redeem_pk)?,
                },
            })),
        }
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> Descriptor<Pk> {
    /// Computes the Bitcoin address of the descriptor, if one exists
    pub fn address(&self, network: &'static AddressParams) -> Option<elements::Address> {
        match *self {
            Descriptor::Bare(..) => None,
            Descriptor::Pk(..) => None,
            Descriptor::Pkh(ref pk) => {
                Some(elements::Address::p2pkh(&pk.to_public_key(), None, network))
            }
            Descriptor::Wpkh(ref pk) => Some(elements::Address::p2wpkh(
                &pk.to_public_key(),
                None,
                network,
            )),
            Descriptor::ShWpkh(ref pk) => Some(elements::Address::p2shwpkh(
                &pk.to_public_key(),
                None,
                network,
            )),
            Descriptor::Sh(ref miniscript) => {
                Some(elements::Address::p2sh(&miniscript.encode(), None, network))
            }
            Descriptor::Wsh(ref miniscript) => Some(elements::Address::p2wsh(
                &miniscript.encode(),
                None,
                network,
            )),
            Descriptor::ShWsh(ref miniscript) => Some(elements::Address::p2shwsh(
                &miniscript.encode(),
                None,
                network,
            )),
            Descriptor::Cov(ref cov) => Some(cov.commit_ctx.address()),
        }
    }

    /// Computes the scriptpubkey of the descriptor
    pub fn script_pubkey(&self) -> Script {
        match *self {
            Descriptor::Bare(ref d) => d.encode(),
            Descriptor::Pk(ref pk) => script::Builder::new()
                .push_key(&pk.to_public_key())
                .push_opcode(opcodes::all::OP_CHECKSIG)
                .into_script(),
            Descriptor::Pkh(ref pk) => {
                let addr =
                    elements::Address::p2pkh(&pk.to_public_key(), None, &AddressParams::ELEMENTS);
                addr.script_pubkey()
            }
            Descriptor::Wpkh(ref pk) => {
                let addr =
                    elements::Address::p2wpkh(&pk.to_public_key(), None, &AddressParams::ELEMENTS);
                addr.script_pubkey()
            }
            Descriptor::ShWpkh(ref pk) => {
                let addr = elements::Address::p2shwpkh(
                    &pk.to_public_key(),
                    None,
                    &AddressParams::ELEMENTS,
                );
                addr.script_pubkey()
            }
            Descriptor::Sh(ref miniscript) => miniscript.encode().to_p2sh(),
            Descriptor::Wsh(ref miniscript) => miniscript.encode().to_v0_p2wsh(),
            Descriptor::ShWsh(ref miniscript) => miniscript.encode().to_v0_p2wsh().to_p2sh(),
            Descriptor::Cov(ref cov) => cov.commit_ctx.script_pubkey().to_v0_p2wsh(),
        }
    }

    /// Computes the scriptSig that will be in place for an unsigned
    /// input spending an output with this descriptor. For pre-segwit
    /// descriptors, which use the scriptSig for signatures, this
    /// returns the empty script.
    ///
    /// This is used in Segwit transactions to produce an unsigned
    /// transaction whose txid will not change during signing (since
    /// only the witness data will change).
    pub fn unsigned_script_sig(&self) -> Script {
        match *self {
            // non-segwit
            Descriptor::Bare(..)
            | Descriptor::Pk(..)
            | Descriptor::Pkh(..)
            | Descriptor::Sh(..) => Script::new(),
            // pure segwit, empty scriptSig
            Descriptor::Wsh(..) | Descriptor::Wpkh(..) => Script::new(),
            // segwit+p2sh
            Descriptor::ShWpkh(ref pk) => {
                let addr =
                    elements::Address::p2wpkh(&pk.to_public_key(), None, &AddressParams::ELEMENTS);
                let redeem_script = addr.script_pubkey();
                script::Builder::new()
                    .push_slice(&redeem_script[..])
                    .into_script()
            }
            Descriptor::ShWsh(ref d) => {
                let witness_script = d.encode();
                script::Builder::new()
                    .push_slice(&witness_script.to_v0_p2wsh()[..])
                    .into_script()
            }
            Descriptor::Cov(ref _c) => Script::new(),
        }
    }

    /// Computes the "witness script" of the descriptor, i.e. the underlying
    /// script before any hashing is done. For `Bare`, `Pkh` and `Wpkh` this
    /// is the scriptPubkey; for `ShWpkh` and `Sh` this is the redeemScript;
    /// for the others it is the witness script.
    pub fn witness_script(&self) -> Script {
        match *self {
            Descriptor::Bare(..)
            | Descriptor::Pk(..)
            | Descriptor::Pkh(..)
            | Descriptor::Wpkh(..) => self.script_pubkey(),
            Descriptor::ShWpkh(ref pk) => {
                let addr =
                    elements::Address::p2wpkh(&pk.to_public_key(), None, &AddressParams::ELEMENTS);
                addr.script_pubkey()
            }
            Descriptor::Sh(ref d) => d.encode(),
            Descriptor::Wsh(ref d) | Descriptor::ShWsh(ref d) => d.encode(),
            Descriptor::Cov(ref cov) => cov.commit_ctx.script_pubkey(),
        }
    }

    /// Returns satisfying witness and scriptSig to spend an
    /// output controlled by the given descriptor if it possible to
    /// construct one using the satisfier.
    pub fn get_satisfication<S: Satisfier<Pk>>(
        &self,
        satisfier: S,
    ) -> Result<(Vec<Vec<u8>>, Script), Error> {
        fn witness_to_scriptsig(witness: &[Vec<u8>]) -> Script {
            let mut b = script::Builder::new();
            for wit in witness {
                if let Ok(n) = script::read_scriptint(wit) {
                    b = b.push_int(n);
                } else {
                    b = b.push_slice(wit);
                }
            }
            b.into_script()
        }

        match *self {
            Descriptor::Bare(ref d) => {
                let wit = match d.satisfy(satisfier) {
                    Some(wit) => wit,
                    None => return Err(Error::CouldNotSatisfy),
                };
                let script_sig = witness_to_scriptsig(&wit);
                let witness = vec![];
                Ok((witness, script_sig))
            }
            Descriptor::Pk(ref pk) => {
                if let Some(sig) = satisfier.lookup_sig(pk) {
                    let mut sig_vec = sig.0.serialize_der().to_vec();
                    sig_vec.push(sig.1.as_u32() as u8);
                    let script_sig = script::Builder::new()
                        .push_slice(&sig_vec[..])
                        .into_script();
                    let witness = vec![];
                    Ok((witness, script_sig))
                } else {
                    Err(Error::MissingSig(pk.to_public_key()))
                }
            }
            Descriptor::Pkh(ref pk) => {
                if let Some(sig) = satisfier.lookup_sig(pk) {
                    let mut sig_vec = sig.0.serialize_der().to_vec();
                    sig_vec.push(sig.1.as_u32() as u8);
                    let script_sig = script::Builder::new()
                        .push_slice(&sig_vec[..])
                        .push_key(&pk.to_public_key())
                        .into_script();
                    let witness = vec![];
                    Ok((witness, script_sig))
                } else {
                    Err(Error::MissingSig(pk.to_public_key()))
                }
            }
            Descriptor::Wpkh(ref pk) => {
                if let Some(sig) = satisfier.lookup_sig(pk) {
                    let mut sig_vec = sig.0.serialize_der().to_vec();
                    sig_vec.push(sig.1.as_u32() as u8);
                    let script_sig = Script::new();
                    let witness = vec![sig_vec, pk.to_public_key().to_bytes()];
                    Ok((witness, script_sig))
                } else {
                    Err(Error::MissingSig(pk.to_public_key()))
                }
            }
            Descriptor::ShWpkh(ref pk) => {
                if let Some(sig) = satisfier.lookup_sig(pk) {
                    let mut sig_vec = sig.0.serialize_der().to_vec();
                    sig_vec.push(sig.1.as_u32() as u8);
                    let addr = elements::Address::p2wpkh(
                        &pk.to_public_key(),
                        None,
                        &AddressParams::ELEMENTS,
                    );
                    let redeem_script = addr.script_pubkey();

                    let script_sig = script::Builder::new()
                        .push_slice(&redeem_script[..])
                        .into_script();
                    let witness = vec![sig_vec, pk.to_public_key().to_bytes()];
                    Ok((witness, script_sig))
                } else {
                    Err(Error::MissingSig(pk.to_public_key()))
                }
            }
            Descriptor::Sh(ref d) => {
                let mut script_witness = match d.satisfy(satisfier) {
                    Some(wit) => wit,
                    None => return Err(Error::CouldNotSatisfy),
                };
                script_witness.push(d.encode().into_bytes());
                let script_sig = witness_to_scriptsig(&script_witness);
                let witness = vec![];
                Ok((witness, script_sig))
            }
            Descriptor::Wsh(ref d) => {
                let mut witness = match d.satisfy(satisfier) {
                    Some(wit) => wit,
                    None => return Err(Error::CouldNotSatisfy),
                };
                witness.push(d.encode().into_bytes());
                let script_sig = Script::new();
                Ok((witness, script_sig))
            }
            Descriptor::ShWsh(ref d) => {
                let witness_script = d.encode();
                let script_sig = script::Builder::new()
                    .push_slice(&witness_script.to_v0_p2wsh()[..])
                    .into_script();

                let mut witness = match d.satisfy(satisfier) {
                    Some(wit) => wit,
                    None => return Err(Error::CouldNotSatisfy),
                };
                witness.push(witness_script.into_bytes());
                Ok((witness, script_sig))
            }
            // API can be improved, not rquired as of now
            Descriptor::Cov(ref cov) => Ok((cov.clone().finalize(), Script::new())),
        }
    }
    /// Attempts to produce a satisfying witness and scriptSig to spend an
    /// output controlled by the given descriptor; add the data to a given
    /// `TxIn` output.
    pub fn satisfy<S: Satisfier<Pk>>(
        &self,
        txin: &mut elements::TxIn,
        satisfier: S,
    ) -> Result<(), Error> {
        let (witness, script_sig) = self.get_satisfication(satisfier)?;
        txin.witness = elements::TxInWitness::default();
        txin.witness.script_witness = witness;
        txin.script_sig = script_sig;
        Ok(())
    }

    /// Computes an upper bound on the weight of a satisfying witness to the
    /// transaction. Assumes all signatures are 73 bytes, including push opcode
    /// and sighash suffix. Includes the weight of the VarInts encoding the
    /// scriptSig and witness stack length.
    pub fn max_satisfaction_weight(&self) -> usize {
        fn varint_len(n: usize) -> usize {
            bitcoin::VarInt(n as u64).len()
        }

        match *self {
            Descriptor::Bare(ref ms) => {
                let scriptsig_len = ms.max_satisfaction_size(1);
                4 * (varint_len(scriptsig_len) + scriptsig_len)
            }
            Descriptor::Pk(..) => 4 * (1 + 73),
            Descriptor::Pkh(ref pk) => 4 * (1 + 73 + pk.serialized_len()),
            Descriptor::Wpkh(ref pk) => 4 + 1 + 73 + pk.serialized_len(),
            Descriptor::ShWpkh(ref pk) => 4 * 24 + 1 + 73 + pk.serialized_len(),
            Descriptor::Sh(ref ms) => {
                let ss = ms.script_size();
                let push_size = if ss < 76 {
                    1
                } else if ss < 0x100 {
                    2
                } else if ss < 0x10000 {
                    3
                } else {
                    5
                };

                let scriptsig_len = push_size + ss + ms.max_satisfaction_size(1);
                4 * (varint_len(scriptsig_len) + scriptsig_len)
            }
            Descriptor::Wsh(ref ms) => {
                let script_size = ms.script_size();
                4 +  // scriptSig length byte
                    varint_len(script_size) +
                    script_size +
                    varint_len(ms.max_satisfaction_witness_elements()) +
                    ms.max_satisfaction_size(2)
            }
            Descriptor::ShWsh(ref ms) => {
                let script_size = ms.script_size();
                4 * 36
                    + varint_len(script_size)
                    + script_size
                    + varint_len(ms.max_satisfaction_witness_elements())
                    + ms.max_satisfaction_size(2)
            }
            Descriptor::Cov(ref cov) => {
                let script_size = cov.commit_ctx.script_pubkey().len();
                4 * 36 + varint_len(script_size) + script_size + varint_len(11) + 700
            }
        }
    }

    /// Get the `scriptCode` of a transaction output.
    ///
    /// The `scriptCode` is the Script of the previous transaction output being serialized in the
    /// sighash when evaluating a `CHECKSIG` & co. OP code.
    pub fn script_code(&self) -> Script {
        match *self {
            // For "legacy" non-P2SH outputs, it is defined as the txo's scriptPubKey.
            Descriptor::Bare(..) | Descriptor::Pk(..) | Descriptor::Pkh(..) => self.script_pubkey(),
            // For "legacy" P2SH outputs, it is defined as the txo's redeemScript.
            Descriptor::Sh(ref d) => d.encode(),
            // For SegWit outputs, it is defined by bip-0143 (quoted below) and is different from
            // the previous txo's scriptPubKey.
            // The item 5:
            //     - For P2WPKH witness program, the scriptCode is `0x1976a914{20-byte-pubkey-hash}88ac`.
            Descriptor::Wpkh(ref pk) | Descriptor::ShWpkh(ref pk) => {
                let addr =
                    elements::Address::p2pkh(&pk.to_public_key(), None, &&AddressParams::ELEMENTS);
                addr.script_pubkey()
            }
            //     - For P2WSH witness program, if the witnessScript does not contain any `OP_CODESEPARATOR`,
            //       the `scriptCode` is the `witnessScript` serialized as scripts inside CTxOut.
            Descriptor::Wsh(ref d) | Descriptor::ShWsh(ref d) => d.encode(),
            Descriptor::Cov(ref cov) => cov.commit_ctx.script_pubkey(),
        }
    }
}

impl Descriptor<DescriptorPublicKey> {
    /// Derives all wildcard keys in the descriptor using the supplied `child_number`
    pub fn derive(&self, child_number: bip32::ChildNumber) -> Descriptor<DescriptorPublicKey> {
        self.translate_pk(
            |pk| Result::Ok::<DescriptorPublicKey, ()>(pk.clone().derive(child_number)),
            |pk| Result::Ok::<DescriptorPublicKey, ()>(pk.clone().derive(child_number)),
        )
        .expect("Translation fn can't fail.")
    }
}

impl<Pk> expression::FromTree for Descriptor<Pk>
where
    Pk: MiniscriptKey,
    <Pk as FromStr>::Err: ToString,
    <<Pk as MiniscriptKey>::Hash as str::FromStr>::Err: ToString,
{
    /// Parse an expression tree into a descriptor
    fn from_tree(top: &expression::Tree) -> Result<Descriptor<Pk>, Error> {
        match (top.name, top.args.len() as u32) {
            ("pk", 1) => {
                expression::terminal(&top.args[0], |pk| Pk::from_str(pk).map(Descriptor::Pk))
            }
            ("pkh", 1) => {
                expression::terminal(&top.args[0], |pk| Pk::from_str(pk).map(Descriptor::Pkh))
            }
            ("wpkh", 1) => {
                let wpkh = expression::terminal(&top.args[0], |pk| Pk::from_str(pk))?;
                if wpkh.is_uncompressed() {
                    Err(Error::ContextError(ScriptContextError::CompressedOnly))
                } else {
                    Ok(Descriptor::Wpkh(wpkh))
                }
            }
            ("sh", 1) => {
                let newtop = &top.args[0];
                match (newtop.name, newtop.args.len()) {
                    ("wsh", 1) => {
                        let sub = Miniscript::from_tree(&newtop.args[0])?;
                        if sub.ty.corr.base != miniscript::types::Base::B {
                            Err(Error::NonTopLevel(format!("{:?}", sub)))
                        } else {
                            Ok(Descriptor::ShWsh(sub))
                        }
                    }
                    ("wpkh", 1) => {
                        let wpkh = expression::terminal(&newtop.args[0], |pk| Pk::from_str(pk))?;
                        if wpkh.is_uncompressed() {
                            Err(Error::ContextError(ScriptContextError::CompressedOnly))
                        } else {
                            Ok(Descriptor::ShWpkh(wpkh))
                        }
                    }
                    _ => {
                        let sub = Miniscript::from_tree(&top.args[0])?;
                        if sub.ty.corr.base != miniscript::types::Base::B {
                            Err(Error::NonTopLevel(format!("{:?}", sub)))
                        } else {
                            Ok(Descriptor::Sh(sub))
                        }
                    }
                }
            }
            ("wsh", 1) => {
                let sub = Miniscript::from_tree(&top.args[0])?;
                if sub.ty.corr.base != miniscript::types::Base::B {
                    Err(Error::NonTopLevel(format!("{:?}", sub)))
                } else {
                    Ok(Descriptor::Wsh(sub))
                }
            }
            _ => {
                let sub = Miniscript::from_tree(&top)?;
                if sub.ty.corr.base != miniscript::types::Base::B {
                    Err(Error::NonTopLevel(format!("{:?}", sub)))
                } else {
                    Ok(Descriptor::Bare(sub))
                }
            } //TODO: If required add string parsing logic
        }
    }
}

impl<Pk> FromStr for Descriptor<Pk>
where
    Pk: MiniscriptKey,
    <Pk as FromStr>::Err: ToString,
    <<Pk as MiniscriptKey>::Hash as str::FromStr>::Err: ToString,
{
    type Err = Error;

    fn from_str(s: &str) -> Result<Descriptor<Pk>, Error> {
        for ch in s.as_bytes() {
            if *ch < 20 || *ch > 127 {
                return Err(Error::Unprintable(*ch));
            }
        }

        let top = expression::Tree::from_str(s)?;
        expression::FromTree::from_tree(&top)
    }
}

impl<Pk: MiniscriptKey> fmt::Debug for Descriptor<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Descriptor::Bare(ref sub) => write!(f, "{:?}", sub),
            Descriptor::Pk(ref p) => write!(f, "pk({:?})", p),
            Descriptor::Pkh(ref p) => write!(f, "pkh({:?})", p),
            Descriptor::Wpkh(ref p) => write!(f, "wpkh({:?})", p),
            Descriptor::ShWpkh(ref p) => write!(f, "sh(wpkh({:?}))", p),
            Descriptor::Sh(ref sub) => write!(f, "sh({:?})", sub),
            Descriptor::Wsh(ref sub) => write!(f, "wsh({:?})", sub),
            Descriptor::ShWsh(ref sub) => write!(f, "sh(wsh({:?}))", sub),
            Descriptor::Cov(ref cov) => write!(f, "cov({:?})", cov),
        }
    }
}

impl<Pk: MiniscriptKey> fmt::Display for Descriptor<Pk> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Descriptor::Bare(ref sub) => write!(f, "{}", sub),
            Descriptor::Pk(ref p) => write!(f, "pk({})", p),
            Descriptor::Pkh(ref p) => write!(f, "pkh({})", p),
            Descriptor::Wpkh(ref p) => write!(f, "wpkh({})", p),
            Descriptor::ShWpkh(ref p) => write!(f, "sh(wpkh({}))", p),
            Descriptor::Sh(ref sub) => write!(f, "sh({})", sub),
            Descriptor::Wsh(ref sub) => write!(f, "wsh({})", sub),
            Descriptor::ShWsh(ref sub) => write!(f, "sh(wsh({}))", sub),
            Descriptor::Cov(ref cov) => write!(
                f,
                "cov({}, {})",
                cov.commit_ctx.redeem_pk, cov.commit_ctx.cov_info.traded_asset
            ),
        }
    }
}

serde_string_impl_pk!(Descriptor, "a script descriptor");

#[cfg(test)]
mod tests {
    use super::DescriptorKeyParseError;

    use bitcoin::hashes::hex::FromHex;
    use bitcoin::util::bip32;
    use bitcoin::{self, PublicKey};
    use descriptor::{DescriptorPublicKey, DescriptorSinglePub, DescriptorXPub};
    use elements::opcodes::all::{OP_CLTV, OP_CSV};
    use elements::script::Instruction;
    use std::str::FromStr;
    use {Descriptor, DummyKey};

    #[cfg(feature = "compiler")]
    use policy;

    type StdDescriptor = Descriptor<PublicKey>;
    const TEST_PK: &'static str =
        "pk(020000000000000000000000000000000000000000000000000000000000000002)";

    fn roundtrip_descriptor(s: &str) {
        let desc = Descriptor::<DummyKey>::from_str(&s).unwrap();
        let output = desc.to_string();
        let normalize_aliases = s.replace("c:pk_k(", "pk(").replace("c:pk_h(", "pkh(");
        assert_eq!(normalize_aliases, output);
    }

    #[test]
    fn desc_rtt_tests() {
        roundtrip_descriptor("c:pk_k()");
        roundtrip_descriptor("wsh(pk())");
        roundtrip_descriptor("wsh(c:pk_k())");
        roundtrip_descriptor("c:pk_h()");
    }
    #[test]
    fn parse_descriptor() {
        StdDescriptor::from_str("(").unwrap_err();
        StdDescriptor::from_str("(x()").unwrap_err();
        StdDescriptor::from_str("(\u{7f}()3").unwrap_err();
        StdDescriptor::from_str("pk()").unwrap_err();
        StdDescriptor::from_str("nl:0").unwrap_err(); //issue 63

        StdDescriptor::from_str(TEST_PK).unwrap();

        let uncompressed_pk =
        "0414fc03b8df87cd7b872996810db8458d61da8448e531569c8517b469a119d267be5645686309c6e6736dbd93940707cc9143d3cf29f1b877ff340e2cb2d259cf";

        // Context tests
        StdDescriptor::from_str(&format!("pk({})", uncompressed_pk)).unwrap();
        StdDescriptor::from_str(&format!("pkh({})", uncompressed_pk)).unwrap();
        StdDescriptor::from_str(&format!("sh(pk({}))", uncompressed_pk)).unwrap();
        StdDescriptor::from_str(&format!("wpkh({})", uncompressed_pk)).unwrap_err();
        StdDescriptor::from_str(&format!("sh(wpkh({}))", uncompressed_pk)).unwrap_err();
        StdDescriptor::from_str(&format!("wsh(pk{})", uncompressed_pk)).unwrap_err();
        StdDescriptor::from_str(&format!("sh(wsh(pk{}))", uncompressed_pk)).unwrap_err();
    }

    #[test]
    fn after_is_cltv() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("wsh(after(1000))").unwrap();
        let script = descriptor.witness_script();

        let actual_instructions: Vec<_> = script.instructions().collect();
        let check = actual_instructions.last().unwrap();

        assert_eq!(check, &Ok(Instruction::Op(OP_CLTV)))
    }

    #[test]
    fn older_is_csv() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("wsh(older(1000))").unwrap();
        let script = descriptor.witness_script();

        let actual_instructions: Vec<_> = script.instructions().collect();
        let check = actual_instructions.last().unwrap();

        assert_eq!(check, &Ok(Instruction::Op(OP_CSV)))
    }

    #[test]
    fn roundtrip_tests() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("multi");
        assert_eq!(
            descriptor.unwrap_err().to_string(),
            "unexpected «no arguments given»"
        )
    }

    #[test]
    fn empty_thresh() {
        let descriptor = Descriptor::<bitcoin::PublicKey>::from_str("thresh");
        assert_eq!(
            descriptor.unwrap_err().to_string(),
            "unexpected «no arguments given»"
        )
    }

    #[test]
    fn test_scriptcode() {
        // P2WPKH (from bip143 test vectors)
        let descriptor = Descriptor::<PublicKey>::from_str(
            "wpkh(025476c2e83188368da1ff3e292e7acafcdb3566bb0ad253f62fc70f07aeee6357)",
        )
        .unwrap();
        assert_eq!(
            *descriptor.script_code().as_bytes(),
            Vec::<u8>::from_hex("76a9141d0f172a0ecb48aee1be1f2687d2963ae33f71a188ac").unwrap()[..]
        );

        // P2SH-P2WPKH (from bip143 test vectors)
        let descriptor = Descriptor::<PublicKey>::from_str(
            "sh(wpkh(03ad1d8e89212f0b92c74d23bb710c00662ad1470198ac48c43f7d6f93a2a26873))",
        )
        .unwrap();
        assert_eq!(
            *descriptor.script_code().as_bytes(),
            Vec::<u8>::from_hex("76a91479091972186c449eb1ded22b78e40d009bdf008988ac").unwrap()[..]
        );

        // P2WSH (from bitcoind's `createmultisig`)
        let descriptor = Descriptor::<PublicKey>::from_str(
            "wsh(multi(2,03789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd,03dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a61626))",
        )
        .unwrap();
        assert_eq!(
            *descriptor
                .script_code()
                .as_bytes(),
            Vec::<u8>::from_hex("522103789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd2103dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a6162652ae").unwrap()[..]
        );

        // P2SH-P2WSH (from bitcoind's `createmultisig`)
        let descriptor = Descriptor::<PublicKey>::from_str("sh(wsh(multi(2,03789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd,03dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a61626)))").unwrap();
        assert_eq!(
            *descriptor
                .script_code()
                .as_bytes(),
            Vec::<u8>::from_hex("522103789ed0bb717d88f7d321a368d905e7430207ebbd82bd342cf11ae157a7ace5fd2103dbc6764b8884a92e871274b87583e6d5c2a58819473e17e107ef3f6aa5a6162652ae")
                .unwrap()[..]
        );
    }

    #[test]
    fn parse_descriptor_key() {
        // With a wildcard
        let key = "[78412e3a/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*";
        let expected = DescriptorPublicKey::XPub(DescriptorXPub {
            origin: Some((
                bip32::Fingerprint::from(&[0x78, 0x41, 0x2e, 0x3a][..]),
                (&[
                    bip32::ChildNumber::from_hardened_idx(44).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                ][..])
                .into(),
            )),
            xpub: bip32::ExtendedPubKey::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            is_wildcard: true,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Without origin
        let key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1";
        let expected = DescriptorPublicKey::XPub(DescriptorXPub {
            origin: None,
            xpub: bip32::ExtendedPubKey::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: (&[bip32::ChildNumber::from_normal_idx(1).unwrap()][..]).into(),
            is_wildcard: false,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Without derivation path
        let key = "xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL";
        let expected = DescriptorPublicKey::XPub(DescriptorXPub {
            origin: None,
            xpub: bip32::ExtendedPubKey::from_str("xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL").unwrap(),
            derivation_path: bip32::DerivationPath::from(&[][..]),
            is_wildcard: false,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Raw (compressed) pubkey
        let key = "03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";
        let expected = DescriptorPublicKey::SinglePub(DescriptorSinglePub {
            key: bitcoin::PublicKey::from_str(
                "03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8",
            )
            .unwrap(),
            origin: None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Raw (uncompressed) pubkey
        let key = "04f5eeb2b10c944c6b9fbcfff94c35bdeecd93df977882babc7f3a2cf7f5c81d3b09a68db7f0e04f21de5d4230e75e6dbe7ad16eefe0d4325a62067dc6f369446a";
        let expected = DescriptorPublicKey::SinglePub(DescriptorSinglePub {
            key: bitcoin::PublicKey::from_str(
                "04f5eeb2b10c944c6b9fbcfff94c35bdeecd93df977882babc7f3a2cf7f5c81d3b09a68db7f0e04f21de5d4230e75e6dbe7ad16eefe0d4325a62067dc6f369446a",
            )
            .unwrap(),
            origin: None,
        });
        assert_eq!(expected, key.parse().unwrap());
        assert_eq!(format!("{}", expected), key);

        // Raw pubkey with origin
        let desc =
            "[78412e3a/0'/42/0']0231c7d3fc85c148717848033ce276ae2b464a4e2c367ed33886cc428b8af48ff8";
        let expected = DescriptorPublicKey::SinglePub(DescriptorSinglePub {
            key: bitcoin::PublicKey::from_str(
                "0231c7d3fc85c148717848033ce276ae2b464a4e2c367ed33886cc428b8af48ff8",
            )
            .unwrap(),
            origin: Some((
                bip32::Fingerprint::from(&[0x78, 0x41, 0x2e, 0x3a][..]),
                (&[
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                    bip32::ChildNumber::from_normal_idx(42).unwrap(),
                    bip32::ChildNumber::from_hardened_idx(0).unwrap(),
                ][..])
                    .into(),
            )),
        });
        assert_eq!(expected, desc.parse().expect("Parsing desc"));
        assert_eq!(format!("{}", expected), desc);
    }

    #[test]
    fn parse_descriptor_key_errors() {
        // We refuse creating descriptors which claim to be able to derive hardened childs
        let desc = "[78412e3a/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/42'/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Hardened derivation is currently not supported."
            ))
        );

        // And even if they they claim it for the wildcard!
        let desc = "[78412e3a/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/42/*'";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Hardened derivation is currently not supported."
            ))
        );

        // And ones with misplaced wildcard
        let desc = "[78412e3a/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*/44";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "\'*\' may only appear as last element in a derivation path."
            ))
        );

        // And ones with invalid fingerprints
        let desc = "[NonHexor]xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Malformed master fingerprint, expected 8 hex chars"
            ))
        );

        // And ones with invalid xpubs..
        let desc = "[78412e3a]xpub1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaLcgJvLJuZZvRcEL/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError("Error while parsing xpub."))
        );

        // ..or invalid raw keys
        let desc = "[78412e3a]0208a117f3897c3a13c9384b8695eed98dc31bc2500feb19a1af424cd47a5d83/1/*";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Error while parsing simple public key"
            ))
        );

        // ..or invalid separators
        let desc = "[78412e3a]]03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8";
        assert_eq!(
            DescriptorPublicKey::from_str(desc),
            Err(DescriptorKeyParseError(
                "Error while parsing simple public key"
            ))
        );
    }

    #[test]
    #[cfg(feature = "compiler")]
    fn parse_and_derive() {
        let descriptor_str = "thresh(2,\
pk([d34db33f/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/*),\
pk(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1),\
pk(03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8))";
        let policy: policy::concrete::Policy<DescriptorPublicKey> = descriptor_str.parse().unwrap();
        let descriptor = Descriptor::Sh(policy.compile().unwrap());
        let derived_descriptor =
            descriptor.derive(bip32::ChildNumber::from_normal_idx(42).unwrap());

        let res_descriptor_str = "thresh(2,\
pk([d34db33f/44'/0'/0']xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1/42),\
pk(xpub6ERApfZwUNrhLCkDtcHTcxd75RbzS1ed54G1LkBUHQVHQKqhMkhgbmJbZRkrgZw4koxb5JaHWkY4ALHY2grBGRjaDMzQLcgJvLJuZZvRcEL/1),\
pk(03f28773c2d975288bc7d1d205c3748651b075fbc6610e58cddeeddf8f19405aa8))";
        let res_policy: policy::concrete::Policy<DescriptorPublicKey> =
            res_descriptor_str.parse().unwrap();
        let res_descriptor = Descriptor::Sh(res_policy.compile().unwrap());

        assert_eq!(res_descriptor, derived_descriptor);
    }
}

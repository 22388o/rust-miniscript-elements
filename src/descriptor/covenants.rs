use bitcoin;
use bitcoin::hashes::hash160;
use bitcoin::secp256k1;
use bitcoin::secp256k1::Secp256k1;
use elements::bitcoin_hashes::{sha256, Hash, HashEngine};
use elements::encode::serialize;
use elements::AddressParams;
use elements::Script;
use elements::{confidential, issuance};
use elements::{SigHash, Transaction, TxOut};
use std::cmp::Ordering;
use {MiniscriptKey, ToPublicKey};

use elements::bip143::SigHashCache;
use elements::script::Builder;
use elements::SigHashType;

const BTC_ASSET: [u8; 32] = [
    0x23, 0x0f, 0x4f, 0x5d, 0x4b, 0x7c, 0x6f, 0xa8, 0x45, 0x80, 0x6e, 0xe4, 0xf6, 0x77, 0x13, 0x45,
    0x9e, 0x1b, 0x69, 0xe8, 0xe6, 0x0f, 0xce, 0xe2, 0xe4, 0x94, 0x0c, 0x7a, 0x0d, 0x5d, 0xe1, 0xb2,
];

/// Covenant Info required while creating a new Covenant
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CovenantCreationCtx {
    /// Asset ID of the c
    pub traded_asset: confidential::Asset,
    pub fee_collector_wsh: Script,
    // server pks
    pub fee_collector_srv_pk: bitcoin::PublicKey,
    pub timestamp_srv_pk: bitcoin::PublicKey,
}

/// All the info required for covenant script/address creation.
/// Does *NOT* include information for witness script creation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CovenantAddressCtx<Pk: MiniscriptKey> {
    /// The creation info
    pub cov_info: CovenantCreationCtx,
    /// The redeem pk
    pub redeem_pk: Pk,
}

impl<Pk: MiniscriptKey + ToPublicKey> CovenantAddressCtx<Pk> {
    /// Get the address corresponding to redeem pk under current context
    pub fn address(&self) -> elements::Address {
        let script_pubkey = cov_scripts::get_covenant_script(&self);
        elements::address::Address::p2wsh(&script_pubkey, None, &AddressParams::ELEMENTS)
    }

    pub fn script_pubkey(&self) -> Script {
        cov_scripts::get_covenant_script(&self)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
/// Struct for containing all information required for spending
/// a covenant.
pub struct CovenantCtx<Pk: MiniscriptKey> {
    /// Must know information about redeem pubkey
    /// for address creation
    pub commit_ctx: CovenantAddressCtx<Pk>,
    /// Optional information only required while spending
    /// the transaction
    pub spend_ctx: Option<CoventSpendCtx<Pk>>,
}

/// Information required for constructing the complete
/// transaction input with witness
#[derive(Clone, Debug)]
pub struct CoventSpendCtx<Pk: MiniscriptKey> {
    // Transaction skeleton
    // These things are to be constructed after the transaction is
    // constructed as they require sighash, signatures etc..
    pub tx: Transaction,
    pub index: usize,
    pub receiver_pk: Pk,
    //amts
    pub sent_amt: confidential::Value,
    pub change_amt: confidential::Value,
    pub fee_amt: confidential::Value,
    pub tx_fee_btc: confidential::Value,

    pub redeem_priv_key: bitcoin::PrivateKey,

    // Sigs and msgs
    pub timestamp_srv_msg: Vec<u8>,
    pub timestamp_srv_sig: Vec<u8>,
    pub fee_srv_msg: Vec<u8>,
    pub fee_srv_sig: Vec<u8>,
}

impl<Pk: MiniscriptKey> PartialEq for CoventSpendCtx<Pk> {
    fn eq(&self, other: &CoventSpendCtx<Pk>) -> bool {
        self.index <= other.index
    }
}

impl<Pk: MiniscriptKey> PartialOrd for CoventSpendCtx<Pk> {
    fn partial_cmp(&self, other: &CoventSpendCtx<Pk>) -> Option<Ordering> {
        Some(self.index.cmp(&other.index))
    }
}

impl<Pk: MiniscriptKey> Eq for CoventSpendCtx<Pk> {}

impl<Pk: MiniscriptKey> Ord for CoventSpendCtx<Pk> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.index.cmp(&other.index)
    }
}

// creates a sig on (time || msg_32)
fn sign_timestamp(txid: [u8; 32]) -> ([u8; 32], secp256k1::Signature) {
    let timestamp_srv_priv_key =
        bitcoin::PrivateKey::from_wif("cMtnxwXc1JEAzRzi6xCGEm4Vig7ECcW4JyczPfyhwpjBiDAJPeDP")
            .unwrap();
    let mut eng = SigHash::engine();
    //  code for get actual time. Format goes here
    let time = [13u8; 32]; // do the encoding stuff properly here
    eng.input(&time);
    eng.input(&txid);
    let msg = secp256k1::Message::from_slice(&sha256::Hash::from_engine(eng)).unwrap();
    let secp = Secp256k1::signing_only();
    (time, secp.sign(&msg, &timestamp_srv_priv_key.key))
}

// Format the fee-into to the desired format
// fee is specified in amount per single-satoshi-fee
// We convert the binary encoding by replacing all ones
// in the binary representation with the positions of ones
// in the system and removing all the zeros.
// We specify fees in 12 bits(2**12 = 4096)
// approximately multiples of 0.025%.
// This assumes that fees must be less than 2^48 (> 2 million BTC).
// Club the fee representation into two groups of 6 bits each
// For example fee = 100 (1 sat per 100 sats sent) or 1%
// Each character is a byte.
// 101 = [0 0 0 0 0  1] [1 0 0 1 0 1] (12 bits total)
//     =  [0 - 1]  [5 2 0 -1] //-1 is split delimiter
//     =  [0 -1 5 2 0 -1] as u8 array.
fn calc_fee_repr(fee: u16) -> Vec<u8> {
    assert!(fee < 4096);
    let r = (fee % 64) as u8;
    let l = (fee / 64) as u8;
    let mut ret = vec![];
    ret.extend(fee_helper(l));
    ret.extend(fee_helper(r));
    ret
}

fn fee_helper(f: u8) -> Vec<u8> {
    assert!(f < 64);
    let mut ret = vec![];
    for i in 5..-1 {
        let mask = 0x01 << i;
        if (mask & f).count_ones() > 1 {
            ret.push(i as u8)
        }
    }
    ret.push(0x4f); //encoding of -1
    ret
}

// Pad a 32 byte blob with timestamp(32 byte) and
// Assumes some encoding of timestamp as 32 bytes
// creates a sig on (time || msg_32)
fn sign_fee(time: [u8; 32]) -> (Vec<u8>, secp256k1::Signature) {
    let fee_collector_srv_priv_key =
        bitcoin::PrivateKey::from_wif("cPNAjBG689Yj71yRwybLvF1uUDVWA9gB2CwDynoUq5CQRNciBa77")
            .unwrap();
    let mut eng = SigHash::engine();
    //  code for get actual time. Format goes here
    let fee = calc_fee_repr(100); // do the encoding stuff properly here
    eng.input(&time);
    eng.input(&fee);
    let msg = secp256k1::Message::from_slice(&sha256::Hash::from_engine(eng)).unwrap();
    let secp = Secp256k1::signing_only();
    (fee, secp.sign(&msg, &fee_collector_srv_priv_key.key))
}

fn get_exp_amt(amt: confidential::Value) -> u64 {
    if let confidential::Value::Explicit(x) = amt {
        x
    } else {
        panic!("Must have explicit amounts");
    }
}

impl<Pk: MiniscriptKey + ToPublicKey> CovenantCtx<Pk> {
    pub fn finalize(&mut self) -> Vec<Vec<u8>> {
        // Set the relevant outputs
        // Must have finalization information

        let btc_ast = confidential::Asset::Explicit(issuance::AssetId::from_inner(
            sha256::Midstate(BTC_ASSET),
        ));
        let mut btc_ast_plus_exp_pref = serialize(&btc_ast);
        btc_ast_plus_exp_pref.push(1u8);

        let pre_code = cov_scripts::pre_code_sep(&self.commit_ctx.cov_info)
            .into_script()
            .into_bytes();
        let script_code = cov_scripts::post_code_sep(
            Builder::new(),
            hash160::Hash::hash(&pre_code).into_inner(),
            self.commit_ctx.redeem_pk.to_public_key(),
        )
        .into_script();

        let script_pubkey = cov_scripts::get_covenant_script(&self.commit_ctx);
        let sighash_msg: Vec<u8>;
        let redeem_sig;
        {
            let ctx = self.spend_ctx.as_mut().unwrap();
            let tx = &mut ctx.tx;
            // The first output must be fee output
            tx.output.push(TxOut::default());
            tx.output[0].asset = self.commit_ctx.cov_info.traded_asset;
            tx.output[0].value = ctx.fee_amt;
            tx.output[0].nonce = confidential::Nonce::Null;
            tx.output[0].script_pubkey = self.commit_ctx.cov_info.fee_collector_wsh.clone();

            tx.output.push(TxOut::default());
            // The second output is reciver amount
            tx.output[1].asset = self.commit_ctx.cov_info.traded_asset;
            tx.output[1].value = ctx.sent_amt;
            tx.output[1].nonce = confidential::Nonce::Null;
            {
                let mut output_ctx = self.commit_ctx.clone();
                // change pk
                output_ctx.redeem_pk = ctx.receiver_pk.clone();
                tx.output[1].script_pubkey =
                    cov_scripts::get_covenant_script(&output_ctx).to_v0_p2wsh();
            }

            tx.output.push(TxOut::default());
            // The third output is the change output
            tx.output[2].asset = self.commit_ctx.cov_info.traded_asset;
            tx.output[2].value = ctx.change_amt;
            tx.output[2].nonce = confidential::Nonce::Null;
            tx.output[2].script_pubkey = script_pubkey.to_v0_p2wsh();

            tx.output.push(TxOut::default());
            // The final output is bitcoin fees output
            tx.output[3].asset = btc_ast;
            tx.output[3].value = ctx.tx_fee_btc;
            tx.output[3].nonce = confidential::Nonce::Null;
            tx.output[3].script_pubkey = Script::new();
        }
        let stk;
        {
            let tx = &self.spend_ctx.as_ref().unwrap().tx;
            let ctx = self.spend_ctx.as_ref().unwrap();
            let mut cache = SigHashCache::new(tx);
            let sighash_type = SigHashType::from_u32(1); //sighash all
            let actual_result = cache.signature_hash(
                0,
                &script_code,
                confidential::Value::Explicit(0x0000000005f5e100),
                sighash_type,
            );
            // let mut enc = SigHash::engine();
            // println!("{:x?}", &actual_result);
            // println!("{:x?}", serialize(&spend_tx.output[0].script_pubkey));
            // assert_eq!(actual_result[8], SigHash::hash(&ser_out).into_inner());
            let secp = Secp256k1::new();
            sighash_msg = actual_result.clone().into_iter().flatten().collect();
            let mut eng = SigHash::engine();
            eng.input(&sighash_msg);
            let sighash_u256 = SigHash::from_engine(eng);

            let sig = secp.sign(
                &bitcoin::secp256k1::Message::from_slice(&sighash_u256[..]).unwrap(),
                &ctx.redeem_priv_key.key,
            );
            redeem_sig = Vec::from(sig.serialize_der().as_ref());

            let mut cache = SigHashCache::new(tx);
            let timestamp_txid = cache.timestamp_txid(sighash_type);
            let (time, timestamp_sig) = sign_timestamp(timestamp_txid.into_inner());
            let (fee, fee_sig) = sign_fee(time);

            let change_amt = get_exp_amt(ctx.change_amt);
            let sent_amt = get_exp_amt(ctx.sent_amt);
            let fee_amt = get_exp_amt(ctx.fee_amt);
            stk = vec![
                redeem_sig,
                serialize(&u64::swap_bytes(change_amt)),
                serialize(&u64::swap_bytes(sent_amt)),
                serialize(&u64::swap_bytes(fee_amt)),
                ctx.receiver_pk.clone().to_public_key().to_bytes(),
                btc_ast_plus_exp_pref,
                Vec::from(&serialize(&tx.output[3])[34..]),
                Vec::from(timestamp_sig.serialize_der().as_ref()),
                Vec::from(time),
                Vec::from(fee),
                Vec::from(fee_sig.serialize_der().as_ref()),
                sighash_msg,
                pre_code,
                script_pubkey.into_bytes(),
            ];
        }
        stk
    }
}

mod cov_scripts {
    use super::{CovenantAddressCtx, CovenantCreationCtx};
    use super::{MiniscriptKey, ToPublicKey};
    use elements::bitcoin_hashes::hash160;
    use elements::bitcoin_hashes::Hash;
    use elements::encode::serialize;
    use elements::opcodes::all::*;
    use elements::script::Builder;
    use elements::Script;

    fn hash_verify(builder: Builder, h: [u8; 20]) -> Builder {
        builder
            .push_opcode(OP_HASH160)
            .push_slice(&h)
            .push_opcode(OP_EQUALVERIFY)
    }
    // Given a script before OP_CODESEP, construct the script after it
    // Assumes the stack structure as
    // [sig sighash pk pre]
    // We have verified all the covenant logic. Now we only need to verify
    // the sighash was constructed correctly.
    pub(super) fn post_code_sep(
        builder: Builder,
        h: [u8; 20],
        redeem_pk: bitcoin::PublicKey,
    ) -> Builder {
        let builder = hash_verify(builder, h);
        // pub pubkey
        assert!(redeem_pk.compressed);
        let builder = builder.push_key(&redeem_pk);

        // Post script
        let builder = builder
            .push_int(2)
            .push_opcode(OP_PICK)
            .push_int(1)
            .push_opcode(OP_CAT)
            .push_opcode(OP_OVER)
            .push_opcode(OP_CHECKSIGVERIFY)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_SHA256)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_CHECKSIGFROMSTACK);
        builder
    }

    pub(super) fn pre_code_sep(ctx: &CovenantCreationCtx) -> Builder {
        let asset = ctx.traded_asset;
        let fee_srv_pk = ctx.fee_collector_srv_pk;
        let fee_collector_wsh = &ctx.fee_collector_wsh;
        let timestamp_srv_pk = ctx.timestamp_srv_pk;
        // let mut stk = vec![ser_sig, serialize(&1000_000_u64), serialize(&98_000_000_u64),serialize(&1000_000_u64), recv_pk, btc_fee_asset, btc_asset_ser, sighash_msg, pre_code];
        let mut stk_size = 13;
        let builder = Builder::new();
        let builder = builder
            .push_opcode(OP_OVER)
            // Now create the post script from script pubkey.
            // The stack contains [sig sighash pre sighash]
            // First get the hashoutputs from sighash
            .push_opcode(OP_DUP);
        stk_size += 2;
        // Calulate the len of post_script by feeding in dummy values
        let post_code_sep_len;
        {
            let pk = bitcoin::PublicKey::from_slice(&[0x02; 33]).unwrap();
            post_code_sep_len =
                serialize(&post_code_sep(Builder::new(), [0u8; 20], pk).into_script()).len();
        }
        let outpoint_start = 4 + 32 + 32 + 32;
        let hashouputs_start = 4 + 32 + 32 + 32 + (32 + 4) + post_code_sep_len + 9 + 4;
        let script_pubkey_start = 4 + 32 + 32 + 32 + (32 + 4) + 1; // assumes 1 byte len

        // Get the custom txid for the transaction onto the alt-stack
        // Calculated as
        // SHA2(version|| hashsequences || hashinputs || hashissuances|| hashoutputs||locktime || sighashflag)
        let builder = builder
            .push_opcode(OP_2DUP)
            .push_int(outpoint_start)
            .push_opcode(OP_LEFT)
            .push_opcode(OP_SWAP)
            .push_int(hashouputs_start as i64)
            .push_opcode(OP_RIGHT)
            .push_opcode(OP_CAT)
            .push_opcode(OP_SHA256)
            .push_opcode(OP_TOALTSTACK);
        let builder = builder
            .push_int(hashouputs_start as i64)
            .push_int(32)
            .push_opcode(OP_SUBSTR)
            .push_opcode(OP_TOALTSTACK);
        stk_size += -1;
        // Next get the change sha2(scriptpubkey)
        let builder = builder
            .push_int(script_pubkey_start)
            .push_int((post_code_sep_len - 1) as i64)
            .push_opcode(OP_SUBSTR)
            .push_opcode(OP_2DUP)
            .push_opcode(OP_CAT)
            // Now the redeem script is top of stack
            .push_opcode(OP_SHA256)
            .push_opcode(OP_TOALTSTACK);
        stk_size += 0;
        // The len
        let pre_publickey_push_len = hash_verify(Builder::new(), [0u8; 20]).into_script().len();
        let builder = builder
            .push_opcode(OP_DUP)
            .push_int((pre_publickey_push_len + 1) as i64) // + 1 for 0x21(len of pk)
            .push_opcode(OP_LEFT)
            .push_int((stk_size + 1) - 5)
            .push_opcode(OP_ROLL)
            //now stack is [.. script_pk pre pk]
            .push_opcode(OP_CAT)
            .push_opcode(OP_SWAP)
            .push_int((pre_publickey_push_len + 34) as i64)
            .push_opcode(OP_RIGHT)
            .push_opcode(OP_CAT)
            .push_opcode(OP_OVER)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_CAT)
            // now stack is [.. script_pk_receiver]
            .push_opcode(OP_SHA256)
            .push_opcode(OP_TOALTSTACK);
        stk_size -= 2;
        // Process the fee output
        let mut pre_value_blob = vec![];
        pre_value_blob.extend(&serialize(&asset)); // asset
        pre_value_blob.push(1u8); // explicit prefix;
        let mut post_value_blob = vec![0u8]; // nonce
        assert!(fee_collector_wsh.is_v0_p2wsh());
        post_value_blob.extend(serialize(fee_collector_wsh));
        let builder = builder.push_slice(&pre_value_blob).push_opcode(OP_DUP);
        stk_size += 2;
        let builder = builder
            .push_int(stk_size - 4)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SIZE)
            .push_int(8)
            .push_opcode(OP_EQUALVERIFY)
            .push_opcode(OP_CAT) // value; deal with this later
            .push_slice(&post_value_blob)
            .push_opcode(OP_CAT)
            .push_opcode(OP_SWAP);
        stk_size += 0;
        // Process the other reiever output
        let builder = builder
            .push_opcode(OP_DUP)
            .push_int((stk_size + 1) - 3)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SIZE)
            .push_int(8)
            .push_opcode(OP_EQUALVERIFY)
            .push_opcode(OP_CAT)
            .push_slice(&[0u8, 34u8, 0u8, 32u8])
            .push_opcode(OP_CAT)
            .push_opcode(OP_FROMALTSTACK)
            .push_opcode(OP_CAT)
            .push_opcode(OP_SWAP);
        stk_size += 1;
        // Get the target and change outputs.
        let builder = builder
            .push_opcode(OP_DUP)
            .push_int((stk_size + 1) - 2)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SIZE)
            .push_int(8)
            .push_opcode(OP_EQUALVERIFY)
            .push_opcode(OP_CAT)
            .push_slice(&[0u8, 34u8, 0u8, 32u8])
            .push_opcode(OP_CAT)
            .push_opcode(OP_FROMALTSTACK)
            .push_opcode(OP_CAT)
            .push_opcode(OP_SWAP);
        // same stk size here as the start
        stk_size += 1;
        let builder = builder
            .push_int(stk_size - 5)
            .push_opcode(OP_ROLL)
            .push_opcode(OP_DUP)
            .push_opcode(OP_ROT)
            .push_opcode(OP_EQUAL)
            .push_int(0)
            .push_opcode(OP_EQUALVERIFY);
        //
        stk_size -= 1;
        let builder = builder
            .push_int(stk_size - 5)
            .push_opcode(OP_ROLL)
            // check size
            .push_opcode(OP_SIZE)
            .push_int(8 + 1 + 1)
            .push_opcode(OP_EQUALVERIFY)
            .push_opcode(OP_CAT);
        stk_size -= 1;

        let builder = builder
            .push_opcode(OP_CAT)
            .push_opcode(OP_CAT)
            .push_opcode(OP_CAT);
        stk_size -= 3;
        // now sighash for hashoutputs in on the top of stack
        let builder = builder
            .push_opcode(OP_HASH256)
            .push_opcode(OP_FROMALTSTACK)
            .push_opcode(OP_EQUALVERIFY);
        stk_size -= 1;
        assert!(stk_size == 10);

        // Now check the sigs and fee calculation
        // Attest that the timestamping server digest is correct
        // The top of stack now contains the timestamp
        // timestamp is assumed to be 32 bytes

        let builder = builder.push_int(stk_size - 5).push_opcode(OP_ROLL);
        let builder = builder
            .push_int(stk_size - 5)
            .push_opcode(OP_PICK)
            .push_opcode(OP_FROMALTSTACK)
            .push_opcode(OP_CAT)
            .push_opcode(OP_SHA256);
        let builder = builder
            .push_key(&timestamp_srv_pk)
            .push_opcode(OP_CHECKSIGFROMSTACKVERIFY);
        stk_size -= 1;

        // Now timestamp sig is check
        let builder = builder
            .push_int(stk_size - 5)
            .push_opcode(OP_ROLL)
            .push_int(stk_size - 5)
            .push_opcode(OP_PICK)
            .push_opcode(OP_CAT)
            .push_opcode(OP_SHA256)
            .push_int(stk_size - 6)
            .push_opcode(OP_ROLL)
            .push_opcode(OP_SWAP);
        let builder = builder
            .push_key(&fee_srv_pk)
            .push_opcode(OP_CHECKSIGFROMSTACKVERIFY);
        // Now timestamp and fee are checkec
        stk_size -= 2;
        // Bring the fee onto the top
        let builder = builder
            .push_int(5)
            .push_opcode(OP_ROLL)
            .push_opcode(OP_DROP);
        stk_size -= 1;

        let builder = builder
            .push_int(stk_size - 2)
            .push_opcode(OP_ROLL)
            .push_opcode(OP_DROP);
        stk_size -= 1;
        let builder = builder
            .push_int(stk_size - 2)
            .push_opcode(OP_ROLL)
            .push_opcode(OP_DROP);
        stk_size -= 1;
        let builder = builder
            .push_int(stk_size - 2)
            .push_opcode(OP_ROLL)
            .push_opcode(OP_DROP);
        // stk_size -= 1;
        builder.push_opcode(OP_CODESEPARATOR)
    }

    pub(super) fn get_covenant_script<Pk: MiniscriptKey + ToPublicKey>(
        ctx: &CovenantAddressCtx<Pk>,
    ) -> Script {
        // Create a covenant that captures value
        // Create a pre-script
        let builder = pre_code_sep(&ctx.cov_info);
        let h = hash160::Hash::hash(&builder.clone().into_script().as_bytes());
        let script =
            post_code_sep(builder, h.into_inner(), ctx.redeem_pk.to_public_key()).into_script();
        script
    }
}

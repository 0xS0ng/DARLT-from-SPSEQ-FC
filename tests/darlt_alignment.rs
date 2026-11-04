//! Clock-free alignment DARLT preparation/online evidence.
use darlt_spseq_fc::{
    darlt::{
        context::ProtocolContext,
        protocol::{self, PublicParameters},
        spend::{self, Atom, Policy},
        verification::Mode,
    },
    ops,
    polynomial::S,
};
use ff::Field;
use rand::{rngs::StdRng, SeedableRng};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeSet, sync::Arc};

#[test]
fn fixed_units_vary_attributes() -> Result<(), String> {
    let mut recorded = Vec::new();
    for attributes in [5, 10, 15, 20, 25, 30] {
        let mut rng = StdRng::seed_from_u64(214_004_000 + attributes as u64);
        let pp = Arc::new(PublicParameters::setup(
            1024,
            16,
            64,
            attributes,
            0,
            b"native-DARLT-alignment",
            &mut rng,
        )?);
        let (ip, key) = protocol::keygen(&pp, &mut rng)?;
        let ip = Arc::new(ip);
        let context = ProtocolContext::new(pp.clone(), ip.clone())?;
        let attrs: Vec<_> = std::iter::once(S::ONE)
            .chain((1..attributes).map(|i| S::from(20 + i as u64)))
            .collect();
        let (request, secret) =
            protocol::prepare_request(&pp, &ip, S::from(91), &attrs, &[], &mut rng)?;
        let response = protocol::issue(&pp, &ip, &key, &request, 1, &mut rng)?;
        let mut wallet = protocol::accept(&pp, &ip, &request, &secret, &response, &mut rng)?;
        let mut child = context.self_derive(&mut wallet, b"all-pools", &[0, 1], &mut rng)?;
        child.holder.scope_opening(&pp, 0)?;
        let policy = Policy {
            period: 1,
            atoms: vec![Atom::Equal(0, S::ONE)],
        };
        let positions: Vec<_> = (0..16).collect();
        ops::reset();
        let prepared =
            spend::prepare_spend(&pp, &ip, &mut child.holder, &positions, &policy, &mut rng)?;
        let preparation = ops::stop();
        ops::reset();
        let token = spend::finish_spend(&pp, &ip, prepared, &[0x42; 32], &mut rng)?;
        let online = ops::stop();
        assert!(context.valid(&token, Mode::Specification, &mut rng));
        assert!(context.valid(&token, Mode::Randomized, &mut rng));
        let wire = token.wire_encode();
        let parsed = spend::Token::wire_decode(&pp, &wire)?;
        assert_eq!(parsed.wire_encode(), wire);
        println!(
            "DARLT_CHECK {}",
            json!({"task":"alignment","construction":"DARLT","phase":"attribute_alignment", "N":1024,"s":16,"k":16,"attributes":attributes,"delegatable_attributes":attributes,"private_attributes":0,"hidden_grants":attributes-1,"range_predicates":0,"actual_pool_queries":1,"actual_offset_queries":16,"timing_enabled":false,"formal_samples":0,"op_counts_enabled":cfg!(feature="op-counts"),"preparation_counts":cfg!(feature="op-counts").then_some(preparation),"online_counts":cfg!(feature="op-counts").then_some(online.clone()),"sigma_variables":token.proof.z.len(),"wire_bytes":wire.len(),"token_sha256":format!("{:x}",Sha256::digest(&wire))})
        );
        recorded.push(online);
    }
    assert_eq!(recorded.len(), 6);
    if cfg!(feature = "op-counts") {
        assert!(recorded.windows(2).all(|pair| pair[0] == pair[1]));
    }
    Ok(())
}

#[test]
fn sequential_pool_workload_records_actual_query_shape() -> Result<(), String> {
    let mut rng = StdRng::seed_from_u64(214_004_777);
    let pp = Arc::new(PublicParameters::setup(
        1024,
        16,
        64,
        5,
        0,
        b"native-sequential-workload",
        &mut rng,
    )?);
    let (ip, key) = protocol::keygen(&pp, &mut rng)?;
    let ip = Arc::new(ip);
    let context = ProtocolContext::new(pp.clone(), ip.clone())?;
    let attrs = [S::ONE, S::from(21), S::from(22), S::from(23), S::from(24)];
    let (request, secret) =
        protocol::prepare_request(&pp, &ip, S::from(91), &attrs, &[], &mut rng)?;
    let response = protocol::issue(&pp, &ip, &key, &request, 1, &mut rng)?;
    let mut wallet = protocol::accept(&pp, &ip, &request, &secret, &response, &mut rng)?;
    let a = context.self_derive(
        &mut wallet,
        b"first-ten-pools",
        &(0..10).collect::<Vec<_>>(),
        &mut rng,
    )?;
    let b = context.self_derive(&mut wallet, b"next-two-pools", &[10, 11], &mut rng)?;
    let mut children = vec![a, b];
    let policy = Policy {
        period: 1,
        atoms: vec![Atom::Equal(0, S::ONE)],
    };
    let mut spent = BTreeSet::new();
    for (scenario, k) in [
        ("initial_pool_prefix", 15),
        ("partial_pool_boundary", 16),
        ("cross64_sequential", 128),
    ] {
        let positions = spend::select_sequential_units(&pp, &children[0].holder, &spent, k)?;
        let expected_shapes = positions
            .chunks(pp.k_max)
            .map(|block| spend::query_shape(&pp, block))
            .collect::<Result<Vec<_>, _>>()?;
        if scenario == "partial_pool_boundary" {
            assert_eq!(positions, (15..31).collect::<Vec<_>>());
            assert_eq!(expected_shapes[0].distinct_pools, 2);
            assert_eq!(expected_shapes[0].distinct_offsets, 16);
            assert_eq!(expected_shapes[0].first_pool_offset, 15);
        }
        let child_id = children[0].id;
        let tokens = context.spend_chunks(
            &mut children,
            vec![(child_id, positions.clone())],
            &policy,
            scenario.as_bytes(),
            scenario.as_bytes(),
            &mut rng,
        )?;
        assert_eq!(tokens.len(), expected_shapes.len());
        for (block, (token, shape)) in tokens.iter().zip(&expected_shapes).enumerate() {
            assert_eq!(token.units.len(), shape.units);
            assert!(context.valid(token, Mode::Specification, &mut rng));
            assert!(context.valid(token, Mode::Randomized, &mut rng));
            let tight_bound = (shape.first_pool_offset + shape.units).div_ceil(pp.s);
            assert!(shape.distinct_pools <= tight_bound);
            println!(
                "DARLT_CHECK {}",
                json!({"task":"alignment","phase":"sequential_query_shape","scenario":scenario,"block":block,"requested_k":k,"block_units":shape.units,"actual_pool_queries":shape.distinct_pools,"actual_offset_queries":shape.distinct_offsets,"start_offset":shape.first_pool_offset,"partial_pool_bound":tight_bound,"timing_enabled":false,"formal_samples":0,"wire_bytes":token.wire_encode().len()})
            );
        }
        assert!(positions.iter().all(|p| spent.insert(*p)));
    }
    let first = spend::select_sequential_units(&pp, &children[0].holder, &spent, 1)?;
    let second = spend::select_sequential_units(&pp, &children[1].holder, &BTreeSet::new(), 16)?;
    let shapes = [
        spend::query_shape(&pp, &first)?,
        spend::query_shape(&pp, &second)?,
    ];
    let requests = vec![(children[0].id, first), (children[1].id, second)];
    let tokens = context.spend_chunks(
        &mut children,
        requests,
        &policy,
        b"cross-child",
        b"cross-child",
        &mut rng,
    )?;
    assert_eq!(
        tokens.len(),
        2,
        "different children must remain separate even below64"
    );
    for (block, (token, shape)) in tokens.iter().zip(shapes).enumerate() {
        assert!(context.valid(token, Mode::Specification, &mut rng));
        println!(
            "DARLT_CHECK {}",
            json!({"task":"alignment","phase":"sequential_query_shape","scenario":"cross_child","block":block,"requested_k":17,"block_units":shape.units,"actual_pool_queries":shape.distinct_pools,"actual_offset_queries":shape.distinct_offsets,"start_offset":shape.first_pool_offset,"actual_child_blocks":2,"timing_enabled":false,"formal_samples":0,"wire_bytes":token.wire_encode().len()})
        );
    }
    assert!(spend::select_sequential_units(&pp, &children[0].holder, &spent, 2).is_err());
    Ok(())
}

//! Section 5-6 of the note: Prop. 5.1, Prop. 5.2, and tightness of Lemma 6.4.
use dual_chain::field::K;
use dual_chain::mle::*;
use dual_chain::poly;
use dual_chain::protocol::*;
use dual_chain::provers::*;
use dual_chain::rng::Rng;

const B: usize = 4;

#[test]
fn fiber_splitting_accepted_without_f1_rejected_with_f1() {
    let mut rng = Rng::new(10);
    for m in 2..=5 {
        let par = Params { m, b: B };
        let fstar = rng.k_vec(1 << m);
        let hstar = hypercube_sum_brute(&fstar, m);
        let h_false = hstar + K::ONE;
        let atk = fiber_attack(par, &fstar, h_false);
        // Construction facts.
        for z in 0..B {
            let direct = eta_coeffs(atk.y[z], m)
                .iter()
                .enumerate()
                .fold(K::ZERO, |acc, (t, &e)| acc + e * K::from_u64(1u64 << (m - (t.count_ones() as usize))));
            assert_eq!(direct, atk.sigma[z], "sigma product formula");
            assert_eq!(hypercube_sum_brute(&atk.g[z], m), h_false, "sum of g_z is H'");
        }
        let d = poly::dist_to_poly(&atk.prover.s0, &fstar);
        assert!((d - B as f64 / par.n() as f64).abs() < 1e-12, "d(s0, F*) = B/n");
        let loose = VerifierConfig { q_b: 32, q_a: 8, terminal: Terminal::OwnFiber };
        let strict = VerifierConfig { q_b: 32, q_a: 8, terminal: Terminal::AllLeavesEqual };
        for _ in 0..10 {
            let mut pr = fiber_attack(par, &fstar, h_false).prover;
            let tr = run(&mut pr, &par, Order::Correct, &mut rng);
            assert_eq!(verify(&tr, &par, &loose, &mut rng), Ok(()), "Pi^- accepts false sum");
            assert_eq!(verify(&tr, &par, &strict, &mut rng), Err("F1: terminal leaves differ".into()));
        }
    }
}

#[test]
fn late_first_round_passes_half_the_paths() {
    let mut rng = Rng::new(11);
    let par = Params { m: 4, b: B };
    let c = rng.k_vec(1 << par.m);
    let h_false = hypercube_sum_brute(&c, par.m) + K::ONE;
    let cfg1 = VerifierConfig { q_b: 8, q_a: 1, terminal: Terminal::AllLeavesEqual };
    let rate = acceptance_rate(|_| LateProver::new(par, &c, h_false), &par, Order::LateFirstRound, &cfg1, 2000, &mut rng);
    assert!((rate - 0.5).abs() < 0.05, "rate = {rate}");
    // Same prover under the correct order cannot use r_1: its (U_1, V_1) come from the honest
    // prover and (a_1) fails on every path.
    let cfg = VerifierConfig { q_b: 8, q_a: 1, terminal: Terminal::AllLeavesEqual };
    let rate_ok = acceptance_rate(|_| LateProver::new(par, &c, h_false), &par, Order::Correct, &cfg, 300, &mut rng);
    assert_eq!(rate_ok, 0.0);
}

#[test]
fn tree_detection_bound_is_tight_at_theta() {
    let mut rng = Rng::new(12);
    let par = Params { m: 4, b: B };
    let fprime = rng.k_vec(1 << par.m);
    let fstar = rng.k_vec(1 << par.m);
    let pr = tightness_prover(par, &fprime, &fstar, &mut rng);
    let d = poly::dist_to_poly(&pr.s0, &fprime);
    assert!((d - 0.375).abs() < 1e-12, "d(s0, F') = 3/8");
    for q in 1..=3 {
        let cfg = VerifierConfig { q_b: q, q_a: 1, terminal: Terminal::AllLeavesEqual };
        let rate = acceptance_rate(
            |rng| tightness_prover(par, &fprime, &fstar, rng),
            &par,
            Order::Correct,
            &cfg,
            3000,
            &mut rng,
        );
        let expect = 0.625f64.powi(q as i32);
        assert!((rate - expect).abs() < 0.04, "q={q}: rate {rate} vs (5/8)^q = {expect}");
    }
}

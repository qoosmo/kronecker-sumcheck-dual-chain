//! Section 1-4 of the note: field, Lemmas 3.1, 3.2, 2.1, Prop. 4.1, honest acceptance.
use dual_chain::chain_b::{butterfly, closed_form_leaf, fold_pair, unfold};
use dual_chain::field::{domain_point, Fp, K, P, W};
use dual_chain::mle::*;
use dual_chain::poly;
use dual_chain::protocol::*;
use dual_chain::provers::FiberProver;
use dual_chain::rng::Rng;

const MS: [usize; 6] = [1, 2, 3, 4, 5, 6];
const B: usize = 4;

#[test]
fn cubic_extension_is_a_field() {
    // x^3 - W irreducible  <=>  W is not a cube  <=>  W^{(p-1)/3} != 1  (3 | p-1).
    assert_eq!((P - 1) % 3, 0);
    assert_ne!(Fp(W).pow((P - 1) / 3), Fp::ONE);
    let mut rng = Rng::new(1);
    for _ in 0..200 {
        let (a, b, c) = (rng.k(), rng.k(), rng.k());
        assert_eq!(a * a.inv(), K::ONE);
        assert_eq!(a * (b + c), a * b + a * c);
        assert_eq!((a * b) * c, a * (b * c));
    }
}

#[test]
fn sum_is_half_point_evaluation() {
    let mut rng = Rng::new(2);
    for m in MS {
        let c = rng.k_vec(1 << m);
        assert_eq!(hypercube_sum_brute(&c, m), half_point_formula(&c, m));
        assert_eq!(partial_sums(&c, m)[0][0], hypercube_sum_brute(&c, m));
    }
}

#[test]
fn lemma_chain_a_identities() {
    let mut rng = Rng::new(3);
    let two = K::from_u64(2);
    for m in MS {
        let c = rng.k_vec(1 << m);
        let r = rng.k_vec(m);
        let a = partial_sums(&c, m);
        assert_eq!(chain_a_p(&a, &r, 0), vec![hypercube_sum_brute(&c, m)]);
        for i in 1..=m {
            let (u, v) = chain_a_uv(&a, &r, i);
            assert_eq!(u.len(), 1 << (i - 1)); // deg <= 2^{i-1} - 1
            let p_prev = chain_a_p(&a, &r, i - 1);
            let p_i = chain_a_p(&a, &r, i);
            // (ii) P_{i-1} = 2U + V
            assert!(poly::eq(&p_prev, &poly::add(&poly::scale(&u, two), &v)), "(ii) m={m} i={i}");
            // (iii) P_i(X) = U(X^2) + r_i X V(X^2)
            let rhs = poly::add(
                &poly::compose_square(&u),
                &poly::scale(&poly::shift(&poly::compose_square(&v)), r[i - 1]),
            );
            assert!(poly::eq(&p_i, &rhs), "(iii) m={m} i={i}");
        }
        // (iv) P_m = f(beta(X))
        assert!(poly::eq(&chain_a_p(&a, &r, m), &beta_poly(&c, &r)));
    }
}

#[test]
fn lambda_unwinds_terminal_to_sum() {
    let mut rng = Rng::new(4);
    for m in MS {
        let c = rng.k_vec(1 << m);
        let r = rng.k_vec(m);
        assert_eq!(unwind(&beta_poly(&c, &r), &r), hypercube_sum_brute(&c, m));
    }
}

#[test]
fn lemma_chain_b_closed_form_and_terminal() {
    let mut rng = Rng::new(5);
    for m in MS {
        let n = B << m;
        let c = rng.k_vec(1 << m);
        let r = rng.k_vec(m);
        let vals: Vec<K> = (0..n).map(|t| poly::eval(&c, domain_point(n, t))).collect();
        let lv = butterfly(&vals, &r);
        for (i, level) in lv.iter().enumerate() {
            let ni = B << (m - i);
            assert_eq!(level.len(), ni);
            for (t, leaf) in level.iter().enumerate() {
                assert_eq!(leaf.len(), 1 << i, "F2 format");
                assert_eq!(*leaf, closed_form_leaf(&c, i, domain_point(ni, t), &r), "m={m} i={i} t={t}");
            }
        }
        let t = beta_poly(&c, &r);
        assert!(lv[m].iter().all(|leaf| *leaf == t), "terminal = f(beta) at every z");
    }
}

#[test]
fn fold_is_injective() {
    let mut rng = Rng::new(6);
    for i in 1..=6 {
        for _ in 0..20 {
            let (a, b) = (rng.k_vec(1 << (i - 1)), rng.k_vec(1 << (i - 1)));
            let (y, r) = (domain_point(64, rng.below(64)), rng.k());
            let s = fold_pair(&a, &b, y, r);
            assert_eq!(s.len(), 1 << i);
            assert_eq!(unfold(&s, y, r), (a, b));
        }
    }
}

#[test]
fn beta_map_is_bijective() {
    // T = f(beta) determines f: invert coefficientwise.
    let mut rng = Rng::new(7);
    for m in MS {
        let c = rng.k_vec(1 << m);
        let r = rng.k_vec(m);
        let t = beta_poly(&c, &r);
        let mut back = vec![K::ZERO; 1 << m];
        for s in 0..1usize << m {
            let (mut e, mut w) = (0usize, K::ONE);
            for k in 1..=m {
                if (s >> (k - 1)) & 1 == 1 {
                    e += 1 << (m - k);
                    w = w * r[k - 1];
                }
            }
            back[s] = t[e] * w.inv();
        }
        assert_eq!(back, c);
    }
}

#[test]
fn honest_prover_is_accepted() {
    let mut rng = Rng::new(8);
    for m in MS {
        let par = Params { m, b: B };
        for term in [Terminal::AllLeavesEqual, Terminal::OwnFiber] {
            let cfg = VerifierConfig { q_b: 16, q_a: 4, terminal: term };
            for _ in 0..3 {
                let c = rng.k_vec(1 << m);
                let mut pr = FiberProver::honest(par, &c);
                let tr = run(&mut pr, &par, Order::Correct, &mut rng);
                assert_eq!(verify(&tr, &par, &cfg, &mut rng), Ok(()));
            }
        }
    }
}

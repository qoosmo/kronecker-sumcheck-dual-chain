//! Report: acceptance rates of the honest prover and of the attacks in the note.
use dual_chain::field::K;
use dual_chain::mle::hypercube_sum_brute;
use dual_chain::protocol::*;
use dual_chain::provers::*;
use dual_chain::rng::Rng;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let m: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(4);
    let trials: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(2000);
    let par = Params { m, b: 4 };
    let mut rng = Rng::new(2026_11_09);
    let f = rng.k_vec(par.l());
    let g = rng.k_vec(par.l());
    let h_false = hypercube_sum_brute(&f, m) + K::ONE;
    let full = |q_b, q_a| VerifierConfig { q_b, q_a, terminal: Terminal::AllLeavesEqual };
    let own = |q_b, q_a| VerifierConfig { q_b, q_a, terminal: Terminal::OwnFiber };

    println!("dual-chain report: m = {m}, B = 4, n = {}, trials = {trials}", par.n());
    println!("{:<46} {:>10} {:>10}", "experiment", "accept", "predicted");
    let row = |name: &str, rate: f64, pred: f64| println!("{name:<46} {rate:>10.4} {pred:>10.4}");

    let r = acceptance_rate(|_| FiberProver::honest(par, &f), &par, Order::Correct, &full(16, 1), trials, &mut rng);
    row("honest, F1 on", r, 1.0);
    let r = acceptance_rate(|_| fiber_attack(par, &f, h_false).prover, &par, Order::Correct, &own(16, 4), trials, &mut rng);
    row("fiber splitting, F1 off (Pi^-)", r, 1.0);
    let r = acceptance_rate(|_| fiber_attack(par, &f, h_false).prover, &par, Order::Correct, &full(16, 4), trials, &mut rng);
    row("fiber splitting, F1 on", r, 0.0);
    for q_a in [1usize, 2, 4] {
        let r = acceptance_rate(|_| LateProver::new(par, &f, h_false), &par, Order::LateFirstRound, &full(8, q_a), trials, &mut rng);
        row(&format!("late (U_1,V_1), q_A = {q_a}"), r, 0.5f64.powi(q_a as i32));
    }
    for q_b in [1usize, 2, 4, 8] {
        let r = acceptance_rate(|rng| tightness_prover(par, &g, &f, rng), &par, Order::Correct, &full(q_b, 1), trials, &mut rng);
        row(&format!("tightness d = 3/8, q = {q_b}"), r, 0.625f64.powi(q_b as i32));
    }
}

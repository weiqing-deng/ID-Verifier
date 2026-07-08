# ID-Verifier

This repository contains the MILP models used to search and verify
impossible-differential attacks on large-state AES-like block ciphers. It
accompanies the anonymous submission on automated impossible-differential
cryptanalysis of Rijndael-256-256 and Vistrutah-256.

## Requirements

The scripts require Python 3, Gurobi, and the Gurobi Python package:

```bash
python3 -m pip install gurobipy
```

A valid Gurobi license is required. If `gurobipy` is installed but the solver
does not start, check the Gurobi license setup.

## Repository Layout

- `Rijndael/milp_rijndael.py`: MILP model for the 10-round
  Rijndael-256-256 attack.
- `Rijndael/results/10R.txt`: saved output for the reported Rijndael run.
- `Vistrutah/milp_vistrutah.py`: MILP model for the 10-round Vistrutah-256
  attack.
- `Vistrutah/results/10R.txt`: saved output for the reported Vistrutah run.

## Running the Models

Run a model from the repository root:

```bash
python3 Rijndael/milp_rijndael.py
python3 Vistrutah/milp_vistrutah.py
```

Each script writes a fresh solver dump to `results/output.txt` under the
corresponding cipher directory. The checked-in `10R.txt` files are saved result
files; keep a separate copy before rerunning if you want to preserve a new
solver output.

The default parameters at the bottom of each script use the 2 + 6 + 2 round
decomposition from the paper: two key-recovery rounds before the distinguisher,
a six-round impossible-differential distinguisher, and two key-recovery rounds
after it.

## Objective Order

The scripts use Gurobi's multi-objective interface. The first objective is
`Obj_time`, with priority 2, so the solver primarily minimizes the logarithmic
time estimate. The second objective is `Obj_data`, with priority 1, so among
solutions with the best time objective the solver prefers a smaller data
objective.

## Structure of the MILP Scripts

The two cipher scripts follow the same organization:

- `Reset_model(...)` initializes the Gurobi model, state variables, complexity
  variables, and key-material counters.
- `Build_distinguisher(...)` builds the generator trail `S1` and calls
  `Build_verifier(...)` to add the embedded verifier trail `S2`.
- `Build_key_recovery(...)` extends the distinguisher to the plaintext and
  ciphertext sides, computes `Delta_P`, `Delta_C`, `cin`, `cout`, and invokes
  key bridging.
- `Build_key_bridging(...)` maps active round-key bytes to independent key
  material and accumulates `K_total`.
- `Set_objective()` adds the data, pair-count, and time constraints and sets
  the objective priorities.
- `Start_solver(...)` runs Gurobi and prints the selected activity pattern and
  objective values.
- `Search_attack(...)` connects the above steps for the default attack
  parameters.

## Reproducibility Notes

To reproduce the paper results directly, some variables corresponding to optimal solutions are fixed in the code. These constraints reduce solving time. Removing them gives a more open search model, but the solver may take much longer to finish.

## Reading the Result Files

The result files are MILP solver dumps. They record the activity patterns and
objective values selected by the model; the paper then turns these patterns
into the attack procedures and final complexity estimates.

The header has the following fields:

- `Model Status`: Gurobi status code. Status `2` means an optimal solution was
  found.
- `Min_Obj`: the optimized primary objective value, on a base-2 logarithmic
  scale.
- `Time`: the model's logarithmic time objective for the selected attack
  pattern.
- `Data`: the logarithmic data objective.
- `N`: the logarithm of the expected number of useful pairs after applying the
  plaintext and ciphertext difference filters.
- `ns`: the logarithm of the number of plaintext structures.
- `Delta_P` and `Delta_C`: the numbers of active bytes in the plaintext and
  ciphertext difference patterns. Byte counts are multiplied by 8 when used as
  bit exponents in the complexity formulas.
- `cin` and `cout`: the independent bit conditions imposed by the top and
  bottom partial computations during key recovery.
- `K_total`: the number of independent active key bytes involved in the sieve.

The matrix blocks use `0` for a zero byte difference and `1` for an active or
unknown byte difference. Each printed state is a 4-by-8 byte state; the vertical
bar separates the two 128-bit halves. For Vistrutah these halves are the left
and right AES-like slices.

- `Var M` is the top key-recovery trail, propagated from the plaintext side to
  the input boundary of the distinguisher.
- `Var W` is the bottom key-recovery trail, propagated from the output boundary
  of the distinguisher toward the ciphertext side.
- `Var S1 | S2` shows the verifier-embedded distinguisher search. `S1` is the
  generator trail that proposes the candidate boundary pattern. `S2` is the
  verifier trail that propagates MDS-induced zero deductions. A candidate is
  accepted only when `S2` proves that at least one byte required active by `S1`
  must be zero at a distinguisher boundary.
- The suffixes `A`, `B`, and `C` denote intermediate states in a round. The
  arrows show the modeled operation between them, such as `(ARK, SB, SR)`,
  `(MC)`, and `(ML)`. For Rijndael the `C` state is identical to `B`; for
  Vistrutah the `ML` arrow is the cipher's mixing layer.
- `Var Key Bridging` records the key bytes selected by the model. Rijndael
  prints `k_guess` and `u_guess` byte masks, while Vistrutah prints the
  `k_target` byte mask.

For the final attack complexities, use the complexity analysis in the paper:
the result files give the MILP-selected activity pattern and logarithmic model
objectives, while the paper also accounts for the concrete sieving algorithms,
the number of impossible trails used, and the master-key recovery step.

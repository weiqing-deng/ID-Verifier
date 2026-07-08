# Starts from Round 1

from gurobipy import Model, GRB, quicksum, LinExpr, QuadExpr, Var
from pathlib import Path
import sys

MODULE_DIR = Path(__file__).resolve().parent
DEFAULT_OUTPUT_PATH = MODULE_DIR / "results" / "output.txt"

rho0 = [9, 7, 13, 14, 0, 10, 3, 5, 1, 2, 15, 4, 6, 12, 11, 8]
rho1 = [12, 8, 1, 9, 15, 4, 0, 3, 14, 10, 6, 7, 2, 5, 13, 11]


def Reset_model(r_in, r_dist, r_out):
    assert r_in >= 1 and r_dist >= 4 and r_out >= 1, "Invalid parameters!"

    global Vistrutah
    Vistrutah = Model("Vistrutah-256")

    # Odd rounds: C[r-1] -- (ARK, SB, SR) -> A[r] -- (MC) -> B[r] -- (==) -> C[r]
    # Even rounds: C[r-1] -- (ARK, SB, SR) -> A[r] -- (MC) -> B[r] -- (ML) -> C[r]
    # Last round: C[r-1] -- (ARK, SB, SR) -> A[r] -- (ARK) -> ciphertext

    global state_S1A, state_S1B, state_S1C
    state_S1A, state_S1B, state_S1C = {}, {}, {}  # VAR S1

    global state_S2A, state_S2B, state_S2C
    state_S2A, state_S2B, state_S2C = {}, {}, {}  # VAR S2

    global state_MA, state_MB, state_MC, state_WA, state_WB, state_WC
    state_MA, state_MB, state_MC = {}, {}, {}  # VAR M
    state_WA, state_WB, state_WC = {}, {}, {}  # VAR W

    global K_total
    K_total = LinExpr()

    global ns, NN, cin, cout, Obj_time, Obj_data
    ns = Vistrutah.addVar(vtype=GRB.INTEGER, name="ns")
    NN = Vistrutah.addVar(vtype=GRB.INTEGER, name="NN")
    cin = Vistrutah.addVar(vtype=GRB.INTEGER, name="cin")
    cout = Vistrutah.addVar(vtype=GRB.INTEGER, name="cout")
    Obj_time = Vistrutah.addVar(vtype=GRB.INTEGER, name="Obj_time")
    Obj_data = Vistrutah.addVar(vtype=GRB.INTEGER, name="Obj_data")

    global Plain_diff, Cipher_diff
    Plain_diff = Vistrutah.addVar(vtype=GRB.INTEGER, name="Plain_diff")
    Cipher_diff = Vistrutah.addVar(vtype=GRB.INTEGER, name="Cipher_diff")


def Evaluate_expr(expr):
    val = 0
    if isinstance(expr, QuadExpr):
        for i in range(expr.size()):
            val += (
                expr.getCoeff(i) * round(expr.getVar1(i).Xn) * round(expr.getVar2(i).Xn)
            )
        val += Evaluate_expr(expr.getLinExpr())
    elif isinstance(expr, LinExpr):
        for i in range(expr.size()):
            val += expr.getCoeff(i) * round(expr.getVar(i).Xn)
        val += expr.getConstant()
    elif isinstance(expr, Var):
        val = round(expr.Xn)
    elif isinstance(expr, (int, float)):
        val = expr
    return val


# var1 = Or(var2)
def Build_mixcolumn_or(var1, var2):
    for i in range(32):
        Vistrutah.addGenConstrOr(
            var1[i],
            [
                var2[4 * (i // 4)],
                var2[4 * (i // 4) + 1],
                var2[4 * (i // 4) + 2],
                var2[4 * (i // 4) + 3],
            ],
        )


def Build_mixcolumn_prob(var_A, var_B, name):
    dummy = Vistrutah.addVars(8, vtype=GRB.BINARY, name=name)
    for i in range(8):
        col_sum = quicksum(var_A[4 * i + j] + var_B[4 * i + j] for j in range(4))
        Vistrutah.addConstr(col_sum >= 5 * dummy[i])
        for j in range(4):
            Vistrutah.addConstr(dummy[i] >= var_A[4 * i + j])
            Vistrutah.addConstr(dummy[i] >= var_B[4 * i + j])
    return dummy


def Calc_zero_count(dummy, var):
    return quicksum(
        4 * dummy[i] - quicksum(var[4 * i + j] for j in range(4)) for i in range(8)
    )


def Build_column_activity(var, name):
    dummy = Vistrutah.addVars(8, vtype=GRB.BINARY, name=name)
    for i in range(8):
        col_sum = quicksum(var[4 * i + j] for j in range(4))
        Vistrutah.addConstr(dummy[i] <= col_sum)
        for j in range(4):
            Vistrutah.addConstr(dummy[i] >= var[4 * i + j])
    return dummy


def Build_s2_assign_by_column_sum(out, ref, lhs, rhs, name, keep=None):
    add_threshold = keep is None
    if keep is None:
        keep = Vistrutah.addVars(8, vtype=GRB.BINARY, name=name)
    for i in range(8):
        if add_threshold:
            col_sum = quicksum(lhs[4 * i + j] + rhs[4 * i + j] for j in range(4))
            Vistrutah.addConstr(col_sum >= 5 * keep[i])
            Vistrutah.addConstr(col_sum <= 4 + 4 * keep[i])
        for j in range(4):
            idx = 4 * i + j
            Vistrutah.addConstr(out[idx] <= ref[idx])
            Vistrutah.addConstr(out[idx] <= keep[i])
            Vistrutah.addConstr(out[idx] >= ref[idx] + keep[i] - 1)
    return keep


# var1 = And(var2)
def Build_mixcolumn_and(var1, var2):
    for i in range(32):
        Vistrutah.addGenConstrAnd(
            var1[i],
            [
                var2[4 * (i // 4)],
                var2[4 * (i // 4) + 1],
                var2[4 * (i // 4) + 2],
                var2[4 * (i // 4) + 3],
            ],
        )


# var1 = Mixing Layer(var2)
def Build_mixing_layer(rd, var1, var2):
    if rd % 2 == 0:  # Even round
        Vistrutah.addConstrs(var1[i] == var2[i * 2] for i in range(16))
        Vistrutah.addConstrs(var1[i + 16] == var2[i * 2 + 1] for i in range(16))
    else:  # Odd round
        Vistrutah.addConstrs(var1[i] == var2[i] for i in range(32))


def SR(i):
    return (i + 4 * (i % 4)) % 16


# var1 = ShiftRow(var2)
def Build_shiftrow(var1, var2):
    for i in range(16):
        Vistrutah.addConstr(var1[i] == var2[SR(i)])
        Vistrutah.addConstr(var1[i + 16] == var2[SR(i) + 16])


# ================= ID Verifier =================
def Build_verifier(r_in, r_dist, r_con):
    r_mid = r_in + r_con
    r_end = r_in + r_dist

    state_S2A[r_mid] = Vistrutah.addVars(
        32, vtype=GRB.BINARY, name=f"state_S2A_{r_mid}"
    )
    state_S2B[r_mid] = Vistrutah.addVars(
        32, vtype=GRB.BINARY, name=f"state_S2B_{r_mid}"
    )
    mid_keep = Build_s2_assign_by_column_sum(
        state_S2A[r_mid],
        state_S1A[r_mid],
        state_S1A[r_mid],
        state_S1B[r_mid],
        "s2_mid_A_keep",
    )
    Build_s2_assign_by_column_sum(
        state_S2B[r_mid],
        state_S1B[r_mid],
        state_S1A[r_mid],
        state_S1B[r_mid],
        "s2_mid_keep",
        mid_keep,
    )

    # S2A[r_mid] -> S2B[r_in]
    for rd in range(r_mid, r_in, -1):
        state_S2C[rd - 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_S2C_{rd-1}"
        )
        state_S2B[rd - 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_S2B_{rd-1}"
        )
        Build_shiftrow(state_S2A[rd], state_S2C[rd - 1])
        Build_mixing_layer(rd - 1, state_S2C[rd - 1], state_S2B[rd - 1])
        if rd - 1 > r_in:
            state_S2A[rd - 1] = Vistrutah.addVars(
                32, vtype=GRB.BINARY, name=f"state_S2A_{rd-1}"
            )
            Build_s2_assign_by_column_sum(
                state_S2A[rd - 1],
                state_S1A[rd - 1],
                state_S2B[rd - 1],
                state_S1A[rd - 1],
                f"s2_back_keep_{rd-1}",
            )

    # S2B[r_mid] -> S2A[r_end]
    for rd in range(r_mid, r_end):
        state_S2C[rd] = Vistrutah.addVars(32, vtype=GRB.BINARY, name=f"state_S2C_{rd}")
        state_S2A[rd + 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_S2A_{rd+1}"
        )
        Build_mixing_layer(rd, state_S2C[rd], state_S2B[rd])
        Build_shiftrow(state_S2A[rd + 1], state_S2C[rd])
        if rd + 1 < r_end:
            state_S2B[rd + 1] = Vistrutah.addVars(
                32, vtype=GRB.BINARY, name=f"state_S2B_{rd+1}"
            )
            Build_s2_assign_by_column_sum(
                state_S2B[rd + 1],
                state_S1B[rd + 1],
                state_S2A[rd + 1],
                state_S1B[rd + 1],
                f"s2_fwd_keep_{rd+1}",
            )

    verifier_drop = Vistrutah.addVars(64, vtype=GRB.BINARY, name="verifier_drop")
    for i in range(32):
        Vistrutah.addConstr(verifier_drop[i] <= state_S1B[r_in][i])
        Vistrutah.addConstr(verifier_drop[i] <= 1 - state_S2B[r_in][i])
        Vistrutah.addConstr(verifier_drop[i] >= state_S1B[r_in][i] - state_S2B[r_in][i])
        Vistrutah.addConstr(verifier_drop[32 + i] <= state_S1A[r_end][i])
        Vistrutah.addConstr(verifier_drop[32 + i] <= 1 - state_S2A[r_end][i])
        Vistrutah.addConstr(
            verifier_drop[32 + i] >= state_S1A[r_end][i] - state_S2A[r_end][i]
        )
    Vistrutah.addConstr(quicksum(verifier_drop[i] for i in range(64)) >= 1)


# ================= Distinguisher =================
def Build_distinguisher(r_in, r_dist, r_con):
    assert r_con >= 1 and r_dist > r_con, "Require 1 <= r_con < r_dist"

    # Forward propagation
    state_S1B[r_in] = Vistrutah.addVars(32, vtype=GRB.BINARY, name=f"state_S1B_{r_in}")
    for rd in range(r_in + 1, r_in + r_con + 1):
        state_S1C[rd - 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_S1C_{rd-1}"
        )
        state_S1A[rd] = Vistrutah.addVars(32, vtype=GRB.BINARY, name=f"state_S1A_{rd}")
        # ML
        Build_mixing_layer(rd - 1, state_S1C[rd - 1], state_S1B[rd - 1])
        # ARK, SB, SR
        Build_shiftrow(state_S1A[rd], state_S1C[rd - 1])
        # MC
        if rd < r_in + r_con:
            state_S1B[rd] = Vistrutah.addVars(
                32, vtype=GRB.BINARY, name=f"state_S1B_{rd}"
            )
            Build_mixcolumn_or(state_S1B[rd], state_S1A[rd])

    # Backward propagation
    state_S1A[r_in + r_dist] = Vistrutah.addVars(
        32, vtype=GRB.BINARY, name=f"state_S1A_{r_in+r_dist}"
    )
    for rd in range(r_in + r_dist, r_in + r_con, -1):
        state_S1C[rd - 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_S1C_{rd-1}"
        )
        state_S1B[rd - 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_S1B_{rd-1}"
        )
        # ARK, SB, SR
        Build_shiftrow(state_S1A[rd], state_S1C[rd - 1])
        # ML
        Build_mixing_layer(rd - 1, state_S1C[rd - 1], state_S1B[rd - 1])
        # MC
        if rd - 1 > r_in + r_con:
            state_S1A[rd - 1] = Vistrutah.addVars(
                32, vtype=GRB.BINARY, name=f"state_S1A_{rd-1}"
            )
            Build_mixcolumn_or(state_S1A[rd - 1], state_S1B[rd - 1])

    Build_verifier(r_in, r_dist, r_con)

    # Non trival
    Vistrutah.addConstr(quicksum(state_S1B[r_in][i] for i in range(32)) >= 1)
    Vistrutah.addConstr(quicksum(state_S1A[r_in + r_dist][i] for i in range(32)) >= 1)


# ================= Key Bridging =================
def Build_key_bridging(r_in, r_dist, r_out, m_c, w_c, w_a, K_res):
    global k_target
    k_target = Vistrutah.addVars(32, vtype=GRB.BINARY, name="k_target")
    target_refs = [[] for _ in range(32)]

    k_even_pos = list(range(16, 32)) + list(range(0, 16))
    r_total = r_in + r_dist + r_out

    for rd in range(r_total + 1):

        def mk_idx(i):
            return k_even_pos[i] if rd % 2 == 0 else i

        if rd < r_in:
            ref_state = m_c[rd]
        elif r_in + r_dist < rd < r_total:
            ref_state = w_c[rd]
        elif rd == r_total:
            ref_state = w_a[rd]
        else:
            ref_state = None

        if ref_state is not None:
            for i in range(32):
                target_refs[mk_idx(i)].append(ref_state[i])

        if rd % 2 == 0:  # Even round key schedule update
            new_k0 = [k_even_pos[i] for i in range(16)]
            new_k1 = [k_even_pos[16 + i] for i in range(16)]
            for i in range(16):
                k_even_pos[i] = new_k0[rho0[i]]
                k_even_pos[16 + i] = new_k1[rho1[i]]

    for idx, refs in enumerate(target_refs):
        if refs:
            for var in refs:
                Vistrutah.addConstr(k_target[idx] >= var)
            Vistrutah.addConstr(k_target[idx] <= quicksum(refs))
        else:
            Vistrutah.addConstr(k_target[idx] == 0)
    K_res.add(quicksum(k_target[i] for i in range(32)))


# ================= Key Recovery =================
def Build_key_recovery(r_in, r_dist, r_out):
    cin_expr = LinExpr()
    cout_expr = LinExpr()

    # VAR M - top rounds
    state_MB[r_in] = Vistrutah.addVars(32, vtype=GRB.BINARY, name=f"state_MB_{r_in}")
    Vistrutah.addConstrs(state_MB[r_in][i] == state_S1B[r_in][i] for i in range(32))

    for rd in range(r_in, 0, -1):
        state_MA[rd] = Vistrutah.addVars(32, vtype=GRB.BINARY, name=f"state_MA_{rd}")
        if rd == r_in:
            dummy = Build_mixcolumn_prob(state_MA[rd], state_MB[rd], f"dummy_MC_M_{rd}")
        else:
            Build_mixcolumn_or(state_MA[rd], state_MB[rd])
            dummy = Build_column_activity(state_MB[rd], f"dummy_MC_M_{rd}")
        cin_expr += Calc_zero_count(dummy, state_MB[rd])

        state_MC[rd - 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_MC_{rd-1}"
        )
        # ARK, SB, SR
        Build_shiftrow(state_MA[rd], state_MC[rd - 1])
        # ML
        if rd > 1:
            state_MB[rd - 1] = Vistrutah.addVars(
                32, vtype=GRB.BINARY, name=f"state_MB_{rd-1}"
            )
            Build_mixing_layer(rd - 1, state_MC[rd - 1], state_MB[rd - 1])

    # Calculate the number of active bytes in the plaintext
    Vistrutah.addConstr(Plain_diff == quicksum(state_MC[0][i] for i in range(32)))

    # VAR W - final rounds
    r_total = r_in + r_dist + r_out
    state_WA[r_in + r_dist] = Vistrutah.addVars(
        32, vtype=GRB.BINARY, name=f"state_WA_{r_in + r_dist}"
    )
    Vistrutah.addConstrs(
        state_WA[r_in + r_dist][i] == state_S1A[r_in + r_dist][i] for i in range(32)
    )

    for rd in range(r_in + r_dist, r_total):
        # MC
        state_WB[rd] = Vistrutah.addVars(32, vtype=GRB.BINARY, name=f"state_WB_{rd}")
        if rd == r_in + r_dist:
            dummy = Build_mixcolumn_prob(state_WA[rd], state_WB[rd], f"dummy_MC_W_{rd}")
        else:
            Build_mixcolumn_or(state_WB[rd], state_WA[rd])
            dummy = Build_column_activity(state_WA[rd], f"dummy_MC_W_{rd}")
        cout_expr += Calc_zero_count(dummy, state_WA[rd])

        # ML
        state_WC[rd] = Vistrutah.addVars(32, vtype=GRB.BINARY, name=f"state_WC_{rd}")
        Build_mixing_layer(rd, state_WC[rd], state_WB[rd])
        # ARK, SB, SR
        state_WA[rd + 1] = Vistrutah.addVars(
            32, vtype=GRB.BINARY, name=f"state_WA_{rd+1}"
        )
        Build_shiftrow(state_WA[rd + 1], state_WC[rd])

    # Calculate the number of active bytes in the ciphertext
    Vistrutah.addConstr(
        Cipher_diff == quicksum(state_WA[r_total][i] for i in range(32))
    )
    Vistrutah.addConstr(cin == 8 * cin_expr)
    Vistrutah.addConstr(cout == 8 * cout_expr)

    Build_key_bridging(
        r_in,
        r_dist,
        r_out,
        state_MC,
        state_WC,
        state_WA,
        K_total,
    )

    # Reasonable
    Vistrutah.addConstr(K_total <= 31)


# Objective function
def Set_objective():
    # D
    Vistrutah.addConstr(Obj_data == ns + 8 * Plain_diff)
    # N
    Vistrutah.addConstr(NN == ns + 16 * Plain_diff - 1 - (256 - 8 * Cipher_diff))
    Vistrutah.addConstr(NN >= cin + cout + 6)  # depend on P
    # T
    Vistrutah.addConstr(Obj_time >= Obj_data)
    Vistrutah.addConstr(Obj_time >= NN + 8 * K_total - (cin + cout) + 24)  # depend on key sieving
    Vistrutah.addConstr(Obj_time >= NN)

    # Objective
    Vistrutah.setObjectiveN(Obj_time, index=0, priority=2, name="Obj_time", weight=1.0)
    Vistrutah.setObjectiveN(Obj_data, index=1, priority=1, name="Obj_data", weight=1.0)
    Vistrutah.ModelSense = GRB.MINIMIZE


def print_block(vals):
    for i in range(4):
        for j in range(4):
            print(vals[4 * j + i], end=" ")
        print("|", end=" ")
        for j in range(4, 8):
            print(vals[4 * j + i], end=" ")
        print("")


def print_var(name, dict):
    print(f"---------- Var {name} ----------")
    for k in sorted(dict):
        print(f"{name}[{k}]")
        print_block([round(dict[k][i].Xn) for i in range(32)])
        print("")


def format_block(vals):
    lines = []
    for i in range(4):
        left = " ".join(str(vals[4 * j + i]) for j in range(4))
        right = " ".join(str(vals[4 * j + i]) for j in range(4, 8))
        lines.append(f"{left} | {right}")
    return lines


def print_key_bridging():
    print("------- Var Key Bridging -------")

    print(
        "k_target     active = {}".format(sum(round(k_target[i].Xn) for i in range(32)))
    )
    print_block([round(k_target[i].Xn) for i in range(32)])
    print("")


def get_flow_timeline(dict_A, dict_B, dict_C):
    timeline = (
        [(r, "A", dict_A[r]) for r in dict_A]
        + [(r, "B", dict_B[r]) for r in dict_B]
        + [(r, "C", dict_C[r]) for r in dict_C]
    )
    timeline.sort(key=lambda x: (x[0], x[1]))
    return timeline


def print_flow(name, dict_A, dict_B, dict_C):
    print(f"------- Var {name} -------")
    timeline = get_flow_timeline(dict_A, dict_B, dict_C)
    for idx, (r, stage, var_dict) in enumerate(timeline):
        print(f"{name}{stage}[{r}]")
        print_block([round(var_dict[i].Xn) for i in range(32)])
        if idx < len(timeline) - 1:
            if stage == "A":
                print("-- (MC) ->")
            elif stage == "B":
                print("-- (ML) ->")
            elif stage == "C":
                print("-- (ARK, SB, SR) ->")
    print("")


def print_flow_pair(name1, dict1_A, dict1_B, dict1_C, name2, dict2_A, dict2_B, dict2_C):
    print(f"------- Var {name1} | {name2} -------")
    flow1 = {
        (r, stage): var
        for r, stage, var in get_flow_timeline(dict1_A, dict1_B, dict1_C)
    }
    flow2 = {
        (r, stage): var
        for r, stage, var in get_flow_timeline(dict2_A, dict2_B, dict2_C)
    }
    keys = sorted(set(flow1) | set(flow2), key=lambda x: (x[0], x[1]))
    width = 23

    for idx, key in enumerate(keys):
        r, stage = key
        label1 = f"{name1}{stage}[{r}]" if key in flow1 else ""
        label2 = f"{name2}{stage}[{r}]" if key in flow2 else ""
        print(f"{label1:<{width}}    {label2}")

        block1 = (
            format_block([round(flow1[key][i].Xn) for i in range(32)])
            if key in flow1
            else [""] * 4
        )
        block2 = (
            format_block([round(flow2[key][i].Xn) for i in range(32)])
            if key in flow2
            else [""] * 4
        )
        for line1, line2 in zip(block1, block2):
            print(f"{line1:<{width}}    {line2}")

        if idx < len(keys) - 1:
            if stage == "A":
                arrow = "-- (MC) ->"
            elif stage == "B":
                arrow = "-- (ML) ->"
            else:
                arrow = "-- (ARK, SB, SR) ->"
            print(f"{arrow:<{width}}    {arrow}")
    print("")


def Start_solver(Print_result):
    Vistrutah.optimize()
    if not Print_result:
        return

    DEFAULT_OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    file = DEFAULT_OUTPUT_PATH.open("w", encoding="utf-8")
    sys.stdout = file
    print("Model Status:", Vistrutah.Status)
    if Vistrutah.Status in [2, 9, 11]:
        print("Min_Obj: %g" % Vistrutah.ObjVal)
        for k in range(Vistrutah.SolCount):
            Vistrutah.Params.SolutionNumber = k
            print(f"******** Solution {k} ********")
            print(
                "******** Time = {}    Data = {}    N = {}    ns = {} ********".format(
                    round(Obj_time.Xn),
                    round(Obj_data.Xn),
                    round(NN.Xn),
                    round(ns.Xn),
                )
            )
            print(
                "******** Delta_P = {}    Delta_C = {} ********".format(
                    round(Evaluate_expr(Plain_diff)),
                    round(Evaluate_expr(Cipher_diff)),
                )
            )
            print(
                "******** cin = {}    cout = {}    K_total = {} ********".format(
                    round(Evaluate_expr(cin)),
                    round(Evaluate_expr(cout)),
                    round(Evaluate_expr(K_total)),
                )
            )

            print_flow("M", state_MA, state_MB, state_MC)
            print_flow_pair(
                "S1",
                state_S1A,
                state_S1B,
                state_S1C,
                "S2",
                state_S2A,
                state_S2B,
                state_S2C,
            )
            print_flow("W", state_WA, state_WB, state_WC)
            print_key_bridging()
    sys.stdout = sys.__stdout__
    file.close()


# def _fix_active_indices(var_dict, rd, active_indices, name):
#     active_set = set(active_indices)
#     if len(active_set) != len(active_indices):
#         raise ValueError(f"Duplicate indices in {name}: {active_indices}")
#     invalid_indices = sorted(i for i in active_set if i < 0 or i >= 32)
#     if invalid_indices:
#         raise ValueError(f"Invalid indices in {name}: {invalid_indices}")

#     for i in range(32):
#         Vistrutah.addConstr(
#             var_dict[rd][i] == int(i in active_set), name=f"fix_{name}_{rd}_{i}"
#         )


def Search_attack(r_in, r_dist, r_con, r_out):
    Reset_model(r_in, r_dist, r_out)
    # Vistrutah.params.OutputFlag = 0
    # Vistrutah.Params.LogToConsole = 0
    Vistrutah.Params.PoolSearchMode = 0
    Vistrutah.Params.PoolSolutions = 1
    # Vistrutah.Params.Threads = 192
    Vistrutah.message("=== Solving Target: " + Vistrutah.ModelName + " ===")
    Vistrutah.message(f"r_in: {r_in}, r_dist: {r_dist}, r_con: {r_con}, r_out: {r_out}")
    Build_distinguisher(r_in, r_dist, r_con)
    Build_key_recovery(r_in, r_dist, r_out)
    Set_objective()
    Start_solver(True)


if __name__ == "__main__":
    r_in = 2
    r_dist = 6
    r_con = 3
    r_out = 2

    # Clear the output file before starting the search
    DEFAULT_OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    DEFAULT_OUTPUT_PATH.write_text("", encoding="utf-8")
    Search_attack(r_in, r_dist, r_con, r_out)

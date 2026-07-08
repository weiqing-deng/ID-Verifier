# Starts from Round 1
# ID attack search for Rijndael with Nk fixed to 8.

from gurobipy import Model, GRB, quicksum, LinExpr, QuadExpr, Var
from pathlib import Path
import sys

MODULE_DIR = Path(__file__).resolve().parent
DEFAULT_OUTPUT_PATH = MODULE_DIR / "results" / "output.txt"


def Reset_model(nb=8, nk=8):
    assert nb in [4, 5, 6, 7, 8] and nk == 8, "Require Nb in [4..8] and Nk = 8"

    global Nb, Nk, Rijndael
    Nb = nb
    Nk = nk
    Rijndael = Model("Rijndael-" + str(32 * Nb) + "-" + str(32 * Nk))

    # Round r:
    # L[r-1] --(ARK, SB, SR)-> A[r] --(MC)-> B[r] = L[r]
    #
    # The C-state dictionaries are kept to mirror Vistrutah's ID model.  For
    # Rijndael there is no MixingLayer, so every C state is constrained equal
    # to the corresponding B state.
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
    ns = Rijndael.addVar(vtype=GRB.INTEGER, name="ns")
    NN = Rijndael.addVar(vtype=GRB.INTEGER, name="NN")
    cin = Rijndael.addVar(vtype=GRB.INTEGER, name="cin")
    cout = Rijndael.addVar(vtype=GRB.INTEGER, name="cout")
    Obj_time = Rijndael.addVar(vtype=GRB.INTEGER, name="Obj_time")
    Obj_data = Rijndael.addVar(vtype=GRB.INTEGER, name="Obj_data")

    global Plain_diff, Cipher_diff
    Plain_diff = Rijndael.addVar(vtype=GRB.INTEGER, name="Plain_diff")
    Cipher_diff = Rijndael.addVar(vtype=GRB.INTEGER, name="Cipher_diff")

    global key_bridge_rounds, key_bridge_state_k0, key_bridge_state_u0
    key_bridge_rounds = 0
    key_bridge_state_k0 = None
    key_bridge_state_u0 = None


def StateSize():
    return 4 * Nb


def BlockSize():
    return 32 * Nb


def Validate_attack_params(r_in, r_dist, r_con, r_out, beta=1):
    assert r_in >= 1 and r_out >= 1, "Require r_in >= 1 and r_out >= 1"
    assert r_con >= 1 and r_dist > r_con, "Require 1 <= r_con < r_dist"
    assert beta >= 0, "Require beta >= 0"


def Normalize_state_bits(matrix, name):
    if matrix is None:
        return None

    rows = list(matrix)
    if len(rows) == StateSize() and all(not isinstance(x, (list, tuple)) for x in rows):
        bits = [int(x) for x in rows]
    elif len(rows) == 4 and all(len(row) == Nb for row in rows):
        bits = [int(rows[row][col]) for col in range(Nb) for row in range(4)]
    elif len(rows) == Nb and all(len(row) == 4 for row in rows):
        bits = [int(rows[col][row]) for col in range(Nb) for row in range(4)]
    else:
        raise ValueError(
            f"{name} must be either a flat {StateSize()}-bit list, "
            f"a 4x{Nb} display matrix, or a {Nb}x4 column matrix"
        )

    invalid = [idx for idx, bit in enumerate(bits) if bit not in (0, 1)]
    if invalid:
        head = ", ".join(str(idx) for idx in invalid[:8])
        raise ValueError(f"{name} has non-0/1 entries at normalized indices: {head}")
    return bits


def Fix_state(var, bits, name):
    if bits is None:
        return
    Rijndael.addConstrs(
        (var[i] == bits[i] for i in range(StateSize())),
        name=f"fix_{name}",
    )


def Fix_distinguisher_endpoints(
    r_in, r_dist, fixed_s1b_r_in=None, fixed_s1a_r_end=None
):
    r_end = r_in + r_dist
    s1b_bits = Normalize_state_bits(fixed_s1b_r_in, "fixed_s1b_r_in")
    s1a_bits = Normalize_state_bits(fixed_s1a_r_end, "fixed_s1a_r_end")
    Fix_state(state_S1B[r_in], s1b_bits, f"state_S1B_{r_in}")
    Fix_state(state_S1A[r_end], s1a_bits, f"state_S1A_{r_end}")


def Fix_key_recovery_states(r_in, r_dist, fixed_ma_r_in=None, fixed_wb_r_end=None):
    r_end = r_in + r_dist
    ma_bits = Normalize_state_bits(fixed_ma_r_in, "fixed_ma_r_in")
    wb_bits = Normalize_state_bits(fixed_wb_r_end, "fixed_wb_r_end")
    Fix_state(state_MA[r_in], ma_bits, f"state_MA_{r_in}")
    Fix_state(state_WB[r_end], wb_bits, f"state_WB_{r_end}")


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


# var1 = Or(var2) column-wise through MixColumns.
def Build_mixcolumn_or(var1, var2):
    for i in range(StateSize()):
        Rijndael.addGenConstrOr(
            var1[i],
            [
                var2[4 * (i // 4)],
                var2[4 * (i // 4) + 1],
                var2[4 * (i // 4) + 2],
                var2[4 * (i // 4) + 3],
            ],
        )


def Build_mixcolumn_prob(var_A, var_B, name):
    dummy = Rijndael.addVars(Nb, vtype=GRB.BINARY, name=name)
    for i in range(Nb):
        col_sum = quicksum(var_A[4 * i + j] + var_B[4 * i + j] for j in range(4))
        Rijndael.addConstr(col_sum >= 5 * dummy[i])
        for j in range(4):
            Rijndael.addConstr(dummy[i] >= var_A[4 * i + j])
            Rijndael.addConstr(dummy[i] >= var_B[4 * i + j])
    return dummy


def Calc_zero_count(dummy, var):
    return quicksum(
        4 * dummy[i] - quicksum(var[4 * i + j] for j in range(4)) for i in range(Nb)
    )


def Build_column_activity(var, name):
    dummy = Rijndael.addVars(Nb, vtype=GRB.BINARY, name=name)
    for i in range(Nb):
        col_sum = quicksum(var[4 * i + j] for j in range(4))
        Rijndael.addConstr(dummy[i] <= col_sum)
        for j in range(4):
            Rijndael.addConstr(dummy[i] >= var[4 * i + j])
    return dummy


def Build_s2_assign_by_column_sum(out, ref, lhs, rhs, name, keep=None):
    add_threshold = keep is None
    if keep is None:
        keep = Rijndael.addVars(Nb, vtype=GRB.BINARY, name=name)
    for i in range(Nb):
        if add_threshold:
            col_sum = quicksum(lhs[4 * i + j] + rhs[4 * i + j] for j in range(4))
            Rijndael.addConstr(col_sum >= 5 * keep[i])
            Rijndael.addConstr(col_sum <= 4 + 4 * keep[i])
        for j in range(4):
            idx = 4 * i + j
            Rijndael.addConstr(out[idx] <= ref[idx])
            Rijndael.addConstr(out[idx] <= keep[i])
            Rijndael.addConstr(out[idx] >= ref[idx] + keep[i] - 1)
    return keep


def Build_round_boundary(var1, var2):
    Rijndael.addConstrs(var1[i] == var2[i] for i in range(StateSize()))


def SR(i):
    if Nb <= 6:
        j = (i + 4 * (i % 4)) % (4 * Nb)
    elif Nb == 7:
        if i % 4 == 0:
            j = i
        elif i % 4 == 1:
            j = (i + 4) % 28
        elif i % 4 == 2:
            j = (i + 8) % 28
        else:
            j = (i + 16) % 28
    else:
        if i % 4 == 0:
            j = i
        elif i % 4 == 1:
            j = (i + 4) % 32
        elif i % 4 == 2:
            j = (i + 12) % 32
        else:
            j = (i + 16) % 32
    return j


# var1 = ShiftRows(var2)
def Build_shiftrow(var1, var2):
    for i in range(StateSize()):
        Rijndael.addConstr(var1[i] == var2[SR(i)])


# ================= ID Verifier =================
def Build_verifier(r_in, r_dist, r_con):
    r_mid = r_in + r_con
    r_end = r_in + r_dist
    n = StateSize()

    state_S2A[r_mid] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_S2A_{r_mid}")
    state_S2B[r_mid] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_S2B_{r_mid}")
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
        "s2_mid_B_keep",
        mid_keep,
    )

    # S2A[r_mid] -> S2B[r_in]
    for rd in range(r_mid, r_in, -1):
        state_S2C[rd - 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_S2C_{rd-1}"
        )
        state_S2B[rd - 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_S2B_{rd-1}"
        )
        Build_shiftrow(state_S2A[rd], state_S2C[rd - 1])
        Build_round_boundary(state_S2C[rd - 1], state_S2B[rd - 1])
        if rd - 1 > r_in:
            state_S2A[rd - 1] = Rijndael.addVars(
                n, vtype=GRB.BINARY, name=f"state_S2A_{rd-1}"
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
        state_S2C[rd] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_S2C_{rd}")
        state_S2A[rd + 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_S2A_{rd+1}"
        )
        Build_round_boundary(state_S2C[rd], state_S2B[rd])
        Build_shiftrow(state_S2A[rd + 1], state_S2C[rd])
        if rd + 1 < r_end:
            state_S2B[rd + 1] = Rijndael.addVars(
                n, vtype=GRB.BINARY, name=f"state_S2B_{rd+1}"
            )
            Build_s2_assign_by_column_sum(
                state_S2B[rd + 1],
                state_S1B[rd + 1],
                state_S2A[rd + 1],
                state_S1B[rd + 1],
                f"s2_fwd_keep_{rd+1}",
            )

    verifier_drop = Rijndael.addVars(2 * n, vtype=GRB.BINARY, name="verifier_drop")
    for i in range(n):
        Rijndael.addConstr(verifier_drop[i] <= state_S1B[r_in][i])
        Rijndael.addConstr(verifier_drop[i] <= 1 - state_S2B[r_in][i])
        Rijndael.addConstr(verifier_drop[i] >= state_S1B[r_in][i] - state_S2B[r_in][i])
        Rijndael.addConstr(verifier_drop[n + i] <= state_S1A[r_end][i])
        Rijndael.addConstr(verifier_drop[n + i] <= 1 - state_S2A[r_end][i])
        Rijndael.addConstr(
            verifier_drop[n + i] >= state_S1A[r_end][i] - state_S2A[r_end][i]
        )
    Rijndael.addConstr(quicksum(verifier_drop[i] for i in range(2 * n)) >= 1)


# ================= Distinguisher =================
def Build_distinguisher(r_in, r_dist, r_con):
    assert r_con >= 1 and r_dist > r_con, "Require 1 <= r_con < r_dist"
    n = StateSize()

    # Forward propagation.
    state_S1B[r_in] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_S1B_{r_in}")
    for rd in range(r_in + 1, r_in + r_con + 1):
        state_S1C[rd - 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_S1C_{rd-1}"
        )
        state_S1A[rd] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_S1A_{rd}")
        Build_round_boundary(state_S1C[rd - 1], state_S1B[rd - 1])
        Build_shiftrow(state_S1A[rd], state_S1C[rd - 1])
        if rd < r_in + r_con:
            state_S1B[rd] = Rijndael.addVars(
                n, vtype=GRB.BINARY, name=f"state_S1B_{rd}"
            )
            Build_mixcolumn_or(state_S1B[rd], state_S1A[rd])

    # Backward propagation.
    r_end = r_in + r_dist
    state_S1A[r_end] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_S1A_{r_end}")
    for rd in range(r_end, r_in + r_con, -1):
        state_S1C[rd - 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_S1C_{rd-1}"
        )
        state_S1B[rd - 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_S1B_{rd-1}"
        )
        Build_shiftrow(state_S1A[rd], state_S1C[rd - 1])
        Build_round_boundary(state_S1C[rd - 1], state_S1B[rd - 1])
        if rd - 1 > r_in + r_con:
            state_S1A[rd - 1] = Rijndael.addVars(
                n, vtype=GRB.BINARY, name=f"state_S1A_{rd-1}"
            )
            Build_mixcolumn_or(state_S1A[rd - 1], state_S1B[rd - 1])

    Build_verifier(r_in, r_dist, r_con)

    # Nontrivial endpoints.
    Rijndael.addConstr(quicksum(state_S1B[r_in][i] for i in range(n)) >= 1)
    Rijndael.addConstr(quicksum(state_S1A[r_end][i] for i in range(n)) >= 1)


# ================= Rijndael-256 Key Bridging =================
def calc(x, y):
    return 4 * x + y


def Get_idx_k(m, x, y, typ):
    a, b = -1, -1
    if typ == 0:
        if x - 8 < 0:
            return -1, -1
        a = calc(x - 8, y)
        if x % 8 == 0:
            b = calc(x - 1, (y + 1) % 4)
        else:
            b = calc(x - 1, y)
    if typ == 1:
        if x + 8 >= m:
            return -1, -1
        a = calc(x + 8, y)
        if x % 8 == 0:
            b = calc(x + 7, (y + 1) % 4)
        else:
            b = calc(x + 7, y)
    if typ == 2:
        if x + 1 >= m or x - 7 < 0:
            return -1, -1
        if x % 8 == 7:
            a = calc(x - 7, (y + 3) % 4)
            b = calc(x + 1, (y + 3) % 4)
        else:
            a = calc(x - 7, y)
            b = calc(x + 1, y)
    if typ == 3:
        if x - 16 < 0 or x % 8 == 0 or x % 8 == 4:
            return -1, -1
        a = calc(x - 16, y)
        if x % 8 == 1:
            b = calc(x - 2, (y + 1) % 4)
        else:
            b = calc(x - 2, y)
    if typ == 4:
        if x + 16 >= m or x % 8 == 0 or x % 8 == 4:
            return -1, -1
        a = calc(x + 16, y)
        if x % 8 == 1:
            b = calc(x + 14, (y + 1) % 4)
        else:
            b = calc(x + 14, y)
    if typ == 5:
        if x + 2 >= m or x - 14 < 0 or x % 8 == 6 or x % 8 == 2:
            return -1, -1
        if x % 8 == 7:
            a = calc(x - 14, (y + 3) % 4)
            b = calc(x + 2, (y + 3) % 4)
        else:
            a = calc(x - 14, y)
            b = calc(x + 2, y)
    if typ == 6:
        if x - 32 < 0 or (x % 8 != 3 and x % 8 != 7):
            return -1, -1
        if x % 8 == 3:
            a = calc(x - 32, y)
            b = calc(x - 4, (y + 1) % 4)
        else:
            a = calc(x - 32, y)
            b = calc(x - 4, y)
    if typ == 7:
        if x + 32 >= m or (x % 8 != 3 and x % 8 != 7):
            return -1, -1
        if x % 8 == 3:
            a = calc(x + 28, (y + 1) % 4)
            b = calc(x + 32, y)
        else:
            a = calc(x + 28, y)
            b = calc(x + 32, y)
    if typ == 8:
        if x + 4 >= m or x - 28 < 0 or (x % 8 != 3 and x % 8 != 7):
            return -1, -1
        if x % 8 == 7:
            a = calc(x - 28, (y + 3) % 4)
            b = calc(x + 4, (y + 3) % 4)
        else:
            a = calc(x - 28, y)
            b = calc(x + 4, y)
    return a, b


def Get_idx_u(m, x, y, typ):
    assert typ <= 5
    a, b = -1, -1
    if typ == 0:
        if x - 8 < 0 or x % 8 == 0 or x % 8 == 4:
            return -1, -1
        a = calc(x - 8, y)
        b = calc(x - 1, y)
    if typ == 1:
        if x + 8 >= m or x % 8 == 0 or x % 8 == 4:
            return -1, -1
        a = calc(x + 7, y)
        b = calc(x + 8, y)
    if typ == 2:
        if x + 1 >= m or x - 7 < 0 or x % 8 == 7 or x % 8 == 3:
            return -1, -1
        a = calc(x - 7, y)
        b = calc(x + 1, y)
    if typ == 3:
        if x - 16 < 0 or x % 8 <= 1 or x % 8 == 4 or x % 8 == 5:
            return -1, -1
        a = calc(x - 16, y)
        b = calc(x - 2, y)
    if typ == 4:
        if x + 16 >= m or x % 8 <= 1 or x % 8 == 4 or x % 8 == 5:
            return -1, -1
        a = calc(x + 14, y)
        b = calc(x + 16, y)
    if typ == 5:
        if x + 2 >= m or x - 14 < 0 or x % 8 >= 6 or x % 8 == 2 or x % 8 == 3:
            return -1, -1
        a = calc(x - 14, y)
        b = calc(x + 2, y)
    return a, b


def Build_key_bridging(beta, r_in, r_dist, r_out, k_in, k_dist, uk_dist, uk_out, K_res):
    # beta: maximum number of key-schedule deduction steps.
    assert beta >= 0, "Require beta >= 0"
    global key_bridge_rounds, key_bridge_state_k0, key_bridge_state_u0

    involved_k = {}
    involved_u = {}
    kb_state_k = {}
    kb_path_k = {}
    kb_state_u = {}
    kb_path_u = {}
    m = Nb * (r_in + r_dist + r_out + 1)
    for i in range(m):
        involved_k[i] = Rijndael.addVars(4, vtype=GRB.BINARY)
        involved_u[i] = Rijndael.addVars(4, vtype=GRB.BINARY)

    for rd in range(r_in + 1):
        for i in range(Nb):
            idx = Nb * rd + i
            if k_in.get(rd) is None:
                Rijndael.addConstrs(involved_k[idx][j] == 0 for j in range(4))
            else:
                Rijndael.addConstrs(
                    involved_k[idx][j] == k_in[rd][4 * i + j] for j in range(4)
                )
            Rijndael.addConstrs(involved_u[idx][j] == 0 for j in range(4))

    for rd in range(1, r_dist):
        for i in range(Nb):
            idx = Nb * (rd + r_in) + i
            if k_dist.get(rd) is None:
                Rijndael.addConstrs(involved_k[idx][j] == 0 for j in range(4))
            else:
                Rijndael.addConstrs(
                    involved_k[idx][j] == k_dist[rd][4 * i + j] for j in range(4)
                )
            if uk_dist.get(rd) is None:
                Rijndael.addConstrs(involved_u[idx][j] == 0 for j in range(4))
            else:
                Rijndael.addConstrs(
                    involved_u[idx][j] == uk_dist[rd][4 * i + j] for j in range(4)
                )

    for rd in range(r_out):
        for i in range(Nb):
            idx = Nb * (rd + r_in + r_dist + 1) + i
            Rijndael.addConstrs(involved_k[idx][j] == 0 for j in range(4))
            if uk_out.get(rd) is None:
                Rijndael.addConstrs(involved_u[idx][j] == 0 for j in range(4))
            else:
                Rijndael.addConstrs(
                    involved_u[idx][j] == uk_out[rd][4 * i + j] for j in range(4)
                )

    n = 4 * m
    kb_state_k[0] = Rijndael.addVars(n, vtype=GRB.BINARY, name="kb_state_k_0")
    kb_state_u[0] = Rijndael.addVars(n, vtype=GRB.BINARY, name="kb_state_u_0")
    for i in range(beta):
        kb_state_k[i + 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"kb_state_k_{i+1}"
        )
        kb_path_k[i + 1] = {}
        for j in range(n):
            kb_path_k[i + 1][j] = Rijndael.addVars(
                10, vtype=GRB.BINARY, name=f"kb_path_k_{i+1}_{j}"
            )
            col = j >> 2
            row = j % 4
            for k in range(9):
                a, b = Get_idx_k(m, col, row, k)
                if a != -1 and b != -1:
                    Rijndael.addGenConstrAnd(
                        kb_path_k[i + 1][j][k],
                        [kb_state_k[i][a], kb_state_k[i][b]],
                    )
                else:
                    Rijndael.addConstr(kb_path_k[i + 1][j][k] == 0)

            expr_sum = quicksum(
                kb_state_k[i][calc(col, r)] for r in range(4)
            ) + quicksum(kb_state_u[i][calc(col, r)] for r in range(4))
            Rijndael.addGenConstrIndicator(
                kb_path_k[i + 1][j][9], True, expr_sum, GRB.GREATER_EQUAL, 4
            )
            Rijndael.addGenConstrIndicator(
                kb_path_k[i + 1][j][9], False, expr_sum, GRB.LESS_EQUAL, 3
            )
            Rijndael.addConstr(kb_state_k[i + 1][j] >= kb_state_k[i][j])
            Rijndael.addConstrs(
                kb_state_k[i + 1][j] >= kb_path_k[i + 1][j][k] for k in range(10)
            )
            Rijndael.addConstr(
                kb_state_k[i + 1][j]
                <= kb_state_k[i][j]
                + quicksum(kb_path_k[i + 1][j][k] for k in range(10))
            )

        kb_state_u[i + 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"kb_state_u_{i+1}"
        )
        kb_path_u[i + 1] = {}
        for j in range(n):
            kb_path_u[i + 1][j] = Rijndael.addVars(
                7, vtype=GRB.BINARY, name=f"kb_path_u_{i+1}_{j}"
            )
            col = j >> 2
            row = j % 4
            for k in range(6):
                a, b = Get_idx_u(m, col, row, k)
                if a != -1 and b != -1:
                    Rijndael.addGenConstrAnd(
                        kb_path_u[i + 1][j][k],
                        [kb_state_u[i][a], kb_state_u[i][b]],
                    )
                else:
                    Rijndael.addConstr(kb_path_u[i + 1][j][k] == 0)

            expr_sum = quicksum(
                kb_state_k[i][calc(col, r)] for r in range(4)
            ) + quicksum(kb_state_u[i][calc(col, r)] for r in range(4))
            Rijndael.addGenConstrIndicator(
                kb_path_u[i + 1][j][6], True, expr_sum, GRB.GREATER_EQUAL, 4
            )
            Rijndael.addGenConstrIndicator(
                kb_path_u[i + 1][j][6], False, expr_sum, GRB.LESS_EQUAL, 3
            )
            Rijndael.addConstr(kb_state_u[i + 1][j] >= kb_state_u[i][j])
            Rijndael.addConstrs(
                kb_state_u[i + 1][j] >= kb_path_u[i + 1][j][k] for k in range(7)
            )
            Rijndael.addConstr(
                kb_state_u[i + 1][j]
                <= kb_state_u[i][j] + quicksum(kb_path_u[i + 1][j][k] for k in range(7))
            )

    for i in range(m):
        Rijndael.addConstrs(
            kb_state_k[beta][4 * i + j] >= involved_k[i][j] for j in range(4)
        )
        Rijndael.addConstrs(
            kb_state_u[beta][4 * i + j] >= involved_u[i][j] for j in range(4)
        )
    K_res.add(
        quicksum(kb_state_k[0][i] for i in range(n))
        + quicksum(kb_state_u[0][i] for i in range(n))
    )

    key_bridge_rounds = r_in + r_dist + r_out + 1
    key_bridge_state_k0 = kb_state_k[0]
    key_bridge_state_u0 = kb_state_u[0]


# ================= Key Recovery =================
def Build_key_recovery(r_in, r_dist, r_out, beta=1):
    assert r_in >= 1 and r_out >= 1, "Require r_in >= 1 and r_out >= 1"
    assert beta >= 0, "Require beta >= 0"
    cin_expr = LinExpr()
    cout_expr = LinExpr()
    n = StateSize()

    # VAR M - initial rounds, backwards from the distinguisher input.
    state_MB[r_in] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_MB_{r_in}")
    Rijndael.addConstrs(state_MB[r_in][i] == state_S1B[r_in][i] for i in range(n))

    for rd in range(r_in, 0, -1):
        state_MA[rd] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_MA_{rd}")
        if rd == r_in:
            dummy = Build_mixcolumn_prob(state_MA[rd], state_MB[rd], f"dummy_MC_M_{rd}")
        else:
            Build_mixcolumn_or(state_MA[rd], state_MB[rd])
            dummy = Build_column_activity(state_MB[rd], f"dummy_MC_M_{rd}")
        cin_expr += Calc_zero_count(dummy, state_MB[rd])

        state_MC[rd - 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_MC_{rd-1}"
        )
        Build_shiftrow(state_MA[rd], state_MC[rd - 1])
        if rd > 1:
            state_MB[rd - 1] = Rijndael.addVars(
                n, vtype=GRB.BINARY, name=f"state_MB_{rd-1}"
            )
            Build_round_boundary(state_MC[rd - 1], state_MB[rd - 1])

    Rijndael.addConstr(Plain_diff == quicksum(state_MC[0][i] for i in range(n)))

    # VAR W - final rounds, forwards from the distinguisher output.
    r_end = r_in + r_dist
    r_total = r_end + r_out
    state_WA[r_end] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_WA_{r_end}")
    Rijndael.addConstrs(state_WA[r_end][i] == state_S1A[r_end][i] for i in range(n))

    for rd in range(r_end, r_total):
        state_WB[rd] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_WB_{rd}")
        if rd == r_end:
            dummy = Build_mixcolumn_prob(state_WA[rd], state_WB[rd], f"dummy_MC_W_{rd}")
        else:
            Build_mixcolumn_or(state_WB[rd], state_WA[rd])
            dummy = Build_column_activity(state_WA[rd], f"dummy_MC_W_{rd}")
        cout_expr += Calc_zero_count(dummy, state_WA[rd])

        state_WC[rd] = Rijndael.addVars(n, vtype=GRB.BINARY, name=f"state_WC_{rd}")
        Build_round_boundary(state_WC[rd], state_WB[rd])
        state_WA[rd + 1] = Rijndael.addVars(
            n, vtype=GRB.BINARY, name=f"state_WA_{rd+1}"
        )
        Build_shiftrow(state_WA[rd + 1], state_WC[rd])

    Rijndael.addConstr(Cipher_diff == quicksum(state_WA[r_total][i] for i in range(n)))
    Rijndael.addConstr(cin == 8 * cin_expr)
    Rijndael.addConstr(cout == 8 * cout_expr)

    # Top extension needs round-key bytes k at linear states L[0..r_in-1].
    # Bottom extension follows the old Rijndael model and uses equivalent-key
    # bytes u for post-SR states after the distinguisher.
    uk_out = {rd - r_end: state_WA[rd + 1] for rd in range(r_end, r_total)}
    Build_key_bridging(beta, r_in, r_dist, r_out, state_MC, {}, {}, uk_out, K_total)

    # Guessing the whole 256-bit key is not a meaningful attack.
    Rijndael.addConstr(K_total <= 31)


# ================= Objective =================
def Set_objective():
    Rijndael.addConstr(Obj_data == ns + 8 * Plain_diff)
    Rijndael.addConstr(NN == ns + 16 * Plain_diff - 1 - (BlockSize() - 8 * Cipher_diff))
    Rijndael.addConstr(NN >= cin + cout + 5)  # depend on P

    Rijndael.addConstr(Obj_time >= Obj_data)
    Rijndael.addConstr(Obj_time >= NN + 8 * K_total - (cin + cout))
    Rijndael.addConstr(Obj_time >= NN)

    Rijndael.setObjectiveN(Obj_time, index=0, priority=2, name="Obj_time", weight=1.0)
    Rijndael.setObjectiveN(Obj_data, index=1, priority=1, name="Obj_data", weight=1.0)
    Rijndael.ModelSense = GRB.MINIMIZE


def _round_key_vals(flat_state, rd):
    vals = []
    for col in range(Nb):
        key_col = Nb * rd + col
        for row in range(4):
            vals.append(round(flat_state[calc(key_col, row)].Xn))
    return vals


def print_block(vals):
    split = 4 if Nb == 8 else Nb
    for i in range(4):
        for j in range(split):
            print(vals[4 * j + i], end=" ")
        if split < Nb:
            print("|", end=" ")
        for j in range(split, Nb):
            print(vals[4 * j + i], end=" ")
        print("")


def format_block(vals):
    split = 4 if Nb == 8 else Nb
    lines = []
    for i in range(4):
        left = " ".join(str(vals[4 * j + i]) for j in range(split))
        if split == Nb:
            lines.append(left)
        else:
            right = " ".join(str(vals[4 * j + i]) for j in range(split, Nb))
            lines.append(f"{left} | {right}")
    return lines


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
        print_block([round(var_dict[i].Xn) for i in range(StateSize())])
        if idx < len(timeline) - 1:
            if stage == "A":
                print("-- (MC) ->")
            elif stage == "B":
                print("-- (=) ->")
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
    width = 4 * Nb + (3 if Nb == 8 else 0) + Nb - 1
    width = max(width, 23)

    for idx, key in enumerate(keys):
        r, stage = key
        label1 = f"{name1}{stage}[{r}]" if key in flow1 else ""
        label2 = f"{name2}{stage}[{r}]" if key in flow2 else ""
        print(f"{label1:<{width}}    {label2}")

        block1 = (
            format_block([round(flow1[key][i].Xn) for i in range(StateSize())])
            if key in flow1
            else [""] * 4
        )
        block2 = (
            format_block([round(flow2[key][i].Xn) for i in range(StateSize())])
            if key in flow2
            else [""] * 4
        )
        for line1, line2 in zip(block1, block2):
            print(f"{line1:<{width}}    {line2}")

        if idx < len(keys) - 1:
            if stage == "A":
                arrow = "-- (MC) ->"
            elif stage == "B":
                arrow = "-- (=) ->"
            else:
                arrow = "-- (ARK, SB, SR) ->"
            print(f"{arrow:<{width}}    {arrow}")
    print("")


def print_key_bridging():
    print("------- Var Key Bridging -------")
    print("K_total = {}".format(round(Evaluate_expr(K_total))))
    if key_bridge_state_k0 is None or key_bridge_state_u0 is None:
        print("")
        return

    for rd in range(key_bridge_rounds):
        vals = _round_key_vals(key_bridge_state_k0, rd)
        if sum(vals) > 0:
            print(f"k_guess[{rd}]")
            print_block(vals)
    for rd in range(key_bridge_rounds):
        vals = _round_key_vals(key_bridge_state_u0, rd)
        if sum(vals) > 0:
            print(f"u_guess[{rd}]")
            print_block(vals)
    print("")


def Start_solver(Print_result=True):
    Rijndael.optimize()
    if not Print_result:
        return

    DEFAULT_OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    file = DEFAULT_OUTPUT_PATH.open("w", encoding="utf-8")
    sys.stdout = file
    print("Model Status:", Rijndael.Status)
    if Rijndael.Status in [2, 9, 11, 13]:
        print("Min_Obj: %g" % Rijndael.ObjVal)
        for k in range(Rijndael.SolCount):
            Rijndael.Params.SolutionNumber = k
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


def Search_attack(
    nb=8,
    nk=8,
    r_in=2,
    r_dist=6,
    r_con=3,
    r_out=2,
    beta=1,
    fixed_s1b_r_in=None,
    fixed_s1a_r_end=None,
    fixed_ma_r_in=None,
    fixed_wb_r_end=None,
):
    Validate_attack_params(r_in, r_dist, r_con, r_out, beta)
    Reset_model(nb, nk)
    Rijndael.Params.PoolSearchMode = 0
    Rijndael.Params.PoolSolutions = 1
    # Rijndael.Params.PoolGap = 0
    Rijndael.message("=== Solving Target: " + Rijndael.ModelName + " ===")
    Rijndael.message(
        f"r_in: {r_in}, r_dist: {r_dist}, r_con: {r_con}, r_out: {r_out}, beta: {beta}"
    )
    Build_distinguisher(r_in, r_dist, r_con)
    Fix_distinguisher_endpoints(r_in, r_dist, fixed_s1b_r_in, fixed_s1a_r_end)
    Build_key_recovery(r_in, r_dist, r_out, beta)
    Fix_key_recovery_states(r_in, r_dist, fixed_ma_r_in, fixed_wb_r_end)
    Set_objective()
    Start_solver(True)


if __name__ == "__main__":
    r_in = 2
    r_dist = 6
    r_con = 3
    r_out = 2
    beta = 1

    fixed_s1b_r_in = None
    fixed_s1a_r_end = None
    fixed_ma_r_in = None
    fixed_wb_r_end = None
    # Example format for fixed endpoints. Rows are printed-state rows; columns
    # are Rijndael columns. Leave either matrix as None if it should be free.
    # Sol 1
    # fixed_ma_r_in = [
    #     [0, 0, 1, 0, 0, 0, 1, 0],
    #     [0, 0, 0, 0, 0, 0, 0, 0],
    #     [0, 0, 0, 0, 0, 0, 0, 0],
    #     [0, 0, 1, 0, 0, 0, 1, 0],
    # ]
    # fixed_s1b_r_in = [
    #     [0, 0, 1, 0, 0, 0, 1, 0],
    #     [0, 0, 0, 0, 0, 0, 1, 0],
    #     [0, 0, 1, 0, 0, 0, 0, 0],
    #     [0, 0, 1, 0, 0, 0, 1, 0],
    # ]
    # fixed_s1a_r_end = [
    #     [0, 0, 0, 0, 0, 0, 0, 0],
    #     [0, 0, 0, 0, 0, 0, 0, 0],
    #     [0, 0, 0, 0, 0, 0, 1, 0],
    #     [0, 0, 0, 0, 0, 0, 0, 0],
    # ]
    # fixed_wb_r_end = [
    #     [0, 0, 0, 0, 0, 0, 1, 0],
    #     [0, 0, 0, 0, 0, 0, 1, 0],
    #     [0, 0, 0, 0, 0, 0, 1, 0],
    #     [0, 0, 0, 0, 0, 0, 1, 0],
    # ]

    DEFAULT_OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    DEFAULT_OUTPUT_PATH.write_text("", encoding="utf-8")
    Search_attack(
        8,
        8,
        r_in,
        r_dist,
        r_con,
        r_out,
        beta,
        fixed_s1b_r_in=fixed_s1b_r_in,
        fixed_s1a_r_end=fixed_s1a_r_end,
        fixed_ma_r_in=fixed_ma_r_in,
        fixed_wb_r_end=fixed_wb_r_end,
    )

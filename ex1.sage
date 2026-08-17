def get_isogeny(K: LaurentSeriesRing, A: int, B: int, c: int, alfa: LaurentSeries, k: list, verbose=True, precision=1000):
    beta = get_beta(c, A, B, alfa)

    list_etas=[]
    list_good_alfa=[]
    
    psi = get_psi(c, A, B, alpha, beta, precision)
    #print("psi=", psi, "\n", "\n", laurent_to_rational(psi)[2], "\n")

    if get_type_of_psi(psi) == -1:
      
        bound_period_psi = get_len(psi)
        
        if bound_period_psi > precision:
            precision = len_period_psi
            print("\n", "precision is now set to be at", bound_period_psi)
        else:
            print("\n", "precision not changed as the bound is", bound_period_psi)

        _,_,len_period_psi, _ = find_period_extended(psi, precision)
        print(len_period_psi, "\n")

        l=test_compatibility(psi, k)
        print("\n", "There are", len(l), "compatible constant terms and hence at most", len(l), "rational isogenies." "\n")
        if len(l) > 0:
            gamma = get_gamma(A, precision, psi)
    
    
            _,_,len_period, _ = find_period_extended(gamma, precision)
    
            if len_period >= 0:
                print("\n", "For the above gamma we got that it is periodic, with period =", len_period, "and we can write it in rational form.")
                print("\n", "gamma=", laurent_to_rational(gamma)[2], "\n")    


                eta = get_eta(c, A, B, precision, alfa, beta, gamma, k)
                if verbose: print("Succes for alfa =", alfa, "...")
                len_eta=len(eta)
                if verbose: print("We recovered ", len_eta, "rational isogenies","\n")
                print("We recovered ", len_eta, "rational isogenies","\n")
                list_good_alfa.append(alfa)

                for i in range (0,len_eta):
                    if verbose: print("======================")
                    if verbose: print("eta #",i,"=", eta[i], "\n")
                
                    if verbose: print("writing eta #",i, "as a rational function", "\n")
                    if verbose: print("\n", "eta=", laurent_to_rational(eta[i])[2], "\n")
                
                if verbose: print("+++++++++++++++++++++")

                list_etas.append(eta)
            else:
                print("Gamma is not periodic", "\n")
                if verbose: print("Alfa=", alfa, "produces a formal solution, but no rational expression is detected")
                return [], []
        else:
            print("The chosen parameters do not satisfy the compatibility conditions")
            return [], []
    else:
        
        str = get_type_of_psi(psi)
        l=test_compatibility(psi, k)
        if verbose: print("Incompatible parameters, due to the fact that ", str, "\n")
        if verbose: print("Also, there are", len(l), "compatible constant terms")
               
        return [], []

    return list_good_alfa, list_etas



def get_len(S):
     i=-1
     p=-1
     if RFG(S)[0] != -1:
         i=int(K(RFG(S)[0]).degree())+1

     if RFG(S)[3] != -1:
         p=int(get_period_bound(K(RFG(S)[Integer(3)]))[4])

     return i+p*3


def get_beta(c: int, A: int, B: int, alfa: LaurentSeries) -> LaurentSeries:
    return (2*A*x^2+c^2*A*x*alfa+O(x^precision))/(2*c^2*(x^3+B+O(x^precision)))

def get_psi(c: int, A: int, B: int, alfa: LaurentSeries, beta: LaurentSeries, precision: int) -> LaurentSeries:
    x = alfa.parent().gen()

    derivative_alfa = derivative(alfa)
    derivative_beta = derivative(beta)

    psi = c^2 * (x^3 + A*x + B + O(x^precision)) * (derivative_alfa + derivative_beta)^2 \
            + 2 * alfa^3 + 2 * beta^3 + 2 * A * alfa + 2 * A * beta + 2 * B + O(x^precision)

    return psi

def get_type_of_psi(psi):
    if psi.valuation()<0:
        return "psi has principal part" 
    if derivative(psi)!=0:
        return "psi is not in V_0"
    return -1 

def get_period_bound(S):
    N = S.precision_absolute()
    val = S.valuation()
    
    if N == +Infinity:
        exp_list = S.exponents()
        if len(exp_list) == 1 and exp_list[0] == -1 and S[-1] == 1:
            return -1, -1, -1, -1, -1, []
            
        is_zero_mod_x = S.is_zero() or all(S[i] == 0 for i in exp_list if i != 0)
    else:
        is_zero_mod_x = S.is_zero() or all(S[i] == 0 for i in range(val, int(N)) if i != 0)
        
    if is_zero_mod_x:
        P_tmp = PolynomialRing(S.parent().base_ring(), S.parent().variable_name())
        return P_tmp(0), 0, P_tmp(1), 0, 0, []

    L = S.parent()
    base_field = L.base_ring()
    var_name = L.variable_name()
    
    P = PolynomialRing(base_field, var_name)
    x = P.gen()
    
    if N == +Infinity:
        exp_list = S.exponents()
        if not exp_list:
            return P(0), 0, P(1), 0, 0, []
        max_exp = max(exp_list)
        coeffs_list = [S[i] for i in range(val, max_exp + 1)]
    else:
        coeffs_list = [S[i] for i in range(val, int(N))]
    
    if len(coeffs_list) % 2 != 0:
        coeffs_list.pop()
        
    if not coeffs_list:
        return P(0), 0, P(1), 0, 0, []
    
    from sage.matrix.berlekamp_massey import berlekamp_massey
    g_rev = berlekamp_massey(coeffs_list)
    d = g_rev.degree()
    
    if d >= len(coeffs_list) // 2:
        raise ValueError("The provided Laurent series is not rational up to the given precision bounds.")
    
    g_bm = P([g_rev[d - i] for i in range(d + 1)])
    poly_series = P(coeffs_list)
    f_bm = (poly_series * g_bm).truncate(poly_series.degree() + 1)
    
    common_gcd = f_bm.gcd(g_bm)
    f_pure = f_bm // common_gcd
    g_pure = g_bm // common_gcd
    
    if val >= 0:
        f_total = f_pure * (x^val)
        g_total = g_pure
    else:
        f_total = f_pure
        g_total = g_pure * (x^(-val))
        
    final_gcd = f_total.gcd(g_total)
    f = f_total // final_gcd
    full_g = g_total // final_gcd
    
    l = 0
    h = full_g
    while h % x == 0 and h != 0:
        h = h // x
        l += 1
        
    if h != 0:
        lc = h.leading_coefficient()
        h = h / lc
        f = f / lc    

    G_bar = GF(3).algebraic_closure()
    subfield, maps = G_bar.subfield(base_field.degree())
    phi = base_field.hom([subfield.gen()], subfield)
    
    P_bar = PolynomialRing(G_bar, var_name)
    h_coeffs_in_closure = [G_bar(phi(c)) for c in h.list()]
    h_in_bar = P_bar(h_coeffs_in_closure)
    
    h_roots_in_closure = h_in_bar.roots()
    factorization_data = []
    
    for alpha_i, m_i in h_roots_in_closure:
        if alpha_i != 0:
            r_i = 1 / alpha_i
            order_r_i = r_i.multiplicative_order()
            factorization_data.append((r_i, m_i, order_r_i))
        
    if factorization_data:
        max_order = max(triple[2] for triple in factorization_data)
        from sage.arith.functions import lcm
        orders = [int(triple[2]) for triple in factorization_data]
        max_m = max(int(triple[1]) for triple in factorization_data)
        
        u = 0
        while 3**u < max_m:
            u += 1
        p_power = 3**u
        
        exact_period = int(lcm(orders + [p_power]))
    else:
        max_order = 0
        exact_period = 1
        
    return f, l, h, max_order, int(exact_period), factorization_data



def RFG(f_laurent):
    if f_laurent.is_zero(): 
        return (0, 0, 1, 0)
    
    L = f_laurent.parent()
    base_field = L.base_ring()
    var_name = L.variable_name()
    
    P = PolynomialRing(base_field, var_name)
    x = P.gen()

    if f_laurent.precision_absolute() == +Infinity:
        exp_list = f_laurent.exponents()
        if len(exp_list) == 1 and exp_list[0] == -1 and f_laurent[-1] == 1:
            return (-1, -1, -1, -1)
    
    N = f_laurent.precision_absolute()
    if N == +Infinity:
        exp_list = f_laurent.exponents()
        if not exp_list:
            return P(0), P(0), P(1), 0
        max_exp = max(exp_list)
        f_poly = P([f_laurent[i] for i in range(max_exp + 1)])
        return f_poly, P(0), P(1), 0
        
    val = f_laurent.valuation()
    
    if val >= 0:
        coeffs_list = [f_laurent[i] for i in range(0, int(N))]
        start_shift = 0
    else:
        coeffs_list = [f_laurent[i] for i in range(val, int(N))]
        start_shift = val

    if len(coeffs_list) % 2 != 0:
        coeffs_list.pop()

    if not coeffs_list:
        return P(0), P(0), P(1), 0

    from sage.matrix.berlekamp_massey import berlekamp_massey
    g_rev = berlekamp_massey(coeffs_list)
    d = g_rev.degree()
    
    g_bm = P([g_rev[d - i] for i in range(d + 1)])
    poly_series = P(coeffs_list)
    f_bm = (poly_series * g_bm).truncate(poly_series.degree() + 1)
    
    if start_shift >= 0:
        f_total = f_bm * (x^start_shift)
        g_total = g_bm
    else:
        f_total = f_bm
        g_total = g_bm * (x^(-start_shift))
        
    common_gcd = f_total.gcd(g_total)
    f_pure = f_total // common_gcd
    g_pure = g_total // common_gcd
    
    R_poly, f = f_pure.quo_rem(g_pure)
    g = g_pure
    
    if g != 0:
        lc = g.leading_coefficient()
        g = g / lc
        f = f / lc
        
    return R_poly, f, g, f/g


def find_period_extended(f, precision) -> (int, list):
    bound=get_len(f)
    if bound < 0:
        return -1, -1
        print("That is not a rational series")

    if bound > precision:
        precision = bound
    
        print("Change the precision")
        return -1, -1

    n = f.prec() if f.prec() is not Infinity else precision
    if n is None or n == 0:
        return 0, []


    list_coeff = [f[i] for i in range(n)]
    
    for period_len in range(n // 2, 0, -1):
        for start_idx in range(n - 2 * period_len + 1):
            remaining_len = n - start_idx
            repeat_count = remaining_len // period_len
            
            if repeat_count < 2:
                continue
                
            end_idx = start_idx + period_len * repeat_count
            
            if list_coeff[start_idx : end_idx - period_len] == list_coeff[start_idx + period_len : end_idx]:
                period = list_coeff[start_idx : start_idx + period_len]
                
                for sub_len in range(1, period_len // 2 + 1):
                    if period_len % sub_len == 0:
                        sub_period = period[:sub_len]
                        if sub_period * (period_len // sub_len) == period:
                            period_len = sub_len
                            period = sub_period
                
                return list_coeff[:start_idx], period, period_len,(start_idx, end_idx - 1)
                
    return None


def find_bound(f):
    bound=get_len(f)
    if bound < 0:
        return -1, -1
        print("That is not a rational series")

    if bound > precision:
        return bound



def get_gamma(A: int, precision: int, psi: LaurentSeries):
    l_psi = psi.list()
    l_gamma = l_psi.copy()
    l_gamma.append(0)

    for i in range(3, len(l_psi), 3):
        if i % 9 != 0:
            l_gamma[i] = K(l_psi[i] / A)
        else:
            if i < len(l_psi):
                gamma_i = l_gamma[i / 3]
                C_3i = l_gamma[i]
                gamma_i_cub = gamma_i ** 3
                element = K(C_3i - gamma_i_cub)
                l_gamma[i] = K(element / A)
            else:
                print(f"Skipping i={i}")

    x = psi.parent().gen()
    reconstructed_series = sum(l_gamma[i] * x**i for i in range(3, len(l_gamma), 3))

    if isinstance(reconstructed_series, int):
        reconstructed_series = K(reconstructed_series)

    return reconstructed_series + O(x^precision)

def test_compatibility(psi: LaurentSeries, k: list) -> list:
    l = []

    #   alfa_1 = derivative(alfa)(0)
    #   rhs = c^2 * B * alfa_1 ^ 2 - B

    for i in k:
        if i^3 + A*i == psi(0):
            l.append(i)

    return l

def get_eta(c: int, A: int, B: int, precision: int, alfa: LaurentSeries, beta: LaurentSeries, gamma: LaurentSeries, k: list):
    free_coeffs = test_compatibility(get_psi(c, A, B, alfa, beta, precision), k)

    eta = []
    for coef in free_coeffs:
        eta.append(K(coef + alfa + beta + gamma))

    return eta


def ver(S, c, K):
    X = S.parent().gen()
    dS_dX = S.derivative()
    Y2 = X^3 + X + 2
    lhs = c^2*Y2*(derivative(S)^2)
    rhs=S^3+S+2
    if lhs==rhs:
        return True
    return False


def laurent_to_rational(S):
    L = S.parent()
    base_field = L.base_ring()
    var_name = L.variable_name()
    
    P = PolynomialRing(base_field, var_name)
    x = P.gen()
    
    if S.is_zero():
        return P(0), P(1), 0

    N = S.precision_absolute()
    if N == +Infinity:
        f_total = P(S.truncate())
        g_total = P(1)
    else:
        val = S.valuation()
        N_fixed = int(N)
        coeffs_list = [S[i] for i in range(val, N_fixed)]
        
        if len(coeffs_list) % 2 != 0:
            coeffs_list.pop()
            
        if not coeffs_list:
            return P(0), P(1), 0
        
        from sage.matrix.berlekamp_massey import berlekamp_massey
        g_rev = berlekamp_massey(coeffs_list)
        d = g_rev.degree()
        
        g_bm = P([g_rev[d - i] for i in range(d + 1)])
        poly_series = P(coeffs_list)
        f_bm = (poly_series * g_bm).truncate(poly_series.degree() + 1)
        
        common_gcd = f_bm.gcd(g_bm)
        f_pure = f_bm // common_gcd
        g_pure = g_bm // common_gcd
        
        if val >= 0:
            f_total = f_pure * (x^val)
            g_total = g_pure
        else:
            f_total = f_pure
            g_total = g_pure * (x^(-val))

    final_gcd = f_total.gcd(g_total)
    f = f_total // final_gcd
    g = g_total // final_gcd
    
    leading_coeff = g.leading_coefficient()
    f = f / leading_coeff
    g = g / leading_coeff
        
    return f, g, f/g


def construct(max_degree, n):
     # Finite field F = GF(3^n)
     F = GF(3^n)     
     R.<x> = LaurentSeriesRing(F)

     series_list = []

     
     from itertools import product

     
     elements = list(F)

     for coeffs in product(elements, repeat=max_degree + 1):
         poly = sum(coeffs[i] * x^i for i in range(max_degree + 1))
         series_list.append(poly)

     return series_list

def generate_iso_with_constraints(max_deg, extension_degree,verbose=False):
    alphas=construct(max_deg,extension_degree)
    l=len(alphas)
    etas=[]
    alfas=[]
    #if verbose: print("Starting.....", datetime.now().strftime("%H:%M:%S"))
    for alpha in alphas:
        a, e=get_isogeny(K,A,B,c,alpha, k,verbose, precision)
        if a!=[] and e!=[]:
            alfas.append(a[0])
            etas.append(e[0])
        
    #if verbose: print("End", datetime.now().strftime("%H:%M:%S"))        
    return l, alfas, etas

def get_parameters_size(alfas, etas):
     contor=0
     for i in range(0,len(etas)):
         contor+=len(etas[i])
     return len(alfas), contor


if __name__ == "__main__":
    p = 3; n = 2; precision = 1000
    A = 1; B = 2; c = 1
    k=[]
    
    from datetime import datetime
    
    K.<x> = LaurentSeriesRing(GF(p^n), "x", default_prec=precision)

    for i in GF(p^n): k.append(i)

    
    max_deg=2
    extension_degree=2
    print("+++++++++++++++++++")
    start=datetime.now()
    print(datetime.now().strftime("%H:%M:%S"))
    
    print("       ⠀⠀⠀⠀⠀⠀⠀   ⢀⣀⣀⣄⣀⡀⠀⠀⠀⠀⠀⠀⠀\n\
          ⠀⠀⠀⠀⢀⣴⠾⠛⠉⠉⠉⠉⠛⠿⣦⡀⠀⠀⠀⠀\n\
          ⠀⠀⠀⢠⡿⠁⠀⢀⣠⣤⣤⣄⡀⠀⠈⢿⡆⠀⠀⠀\n\
⠀          ⠀⢀⣿⣁⣀⣠⡿⠋⠀⠀⠙⢿⣄⣀⣈⣿⡀⠀⠀\n\
⠀          ⠀⢸⣿⠛⠛⢻⣧⠀⠿⠇⠀⣼⡟⠛⠛⣿⡇⠀⠀\n\
⠀          ⠀⢸⣿⠀⠀⠀⠙⢷⣦⣴⡾⠋⠀⠀⠀⣿⡇⠀⠀\n\
⠀          ⠀⢸⣿⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣿⡇⠀⠀\n\
⠀          ⠀⣸⣿⠀⠀⠀⠛⠷⠶⠶⠾⠛⠀⠀⠀⣿⣇⠀⠀\n\
⠀         ⠀⣸⣿⣿⢷⣦⣀⣀⣀⣀⣀⣀⣀⣀⣴⡾⣿⣿⣇⠀\n\
⠀         ⢠⣿⢸⣿⠀⣿⡏⠉⠉⠉⠉⠉⠉⢹⣿⠀⣿⡇⣿⡄\n\
          ⢸⡏⢸⣿⣀⣿⡇⠀⠀⠀⠀⠀⠀⢸⣿⣀⣿⡇⢹⡇\n\
          ⢸⡇⠀⢿⣏⠉⠁⠀⠀⠀⠀⠀⠀⠈⠉⣹⡿⠀⢸⡇\n\
          ⢸⣿⣤⣌⠛⠷⣶⣶⣶⣶⣶⣶⣶⣶⠾⠛⣡⣤⣿⡇\n\
          ⠘⠿⠿⠇⠀⠀⠀⢿⡾⠇⠸⢷⡿⠀⠀⠀⠸⠿⠿⠃\n\
⠀⠀⠀⠀⠀⠀           ⠀⠛⠛⠁⠈⠛⠛⠀⠀⠀⠀⠀⠀⠀")
    
   
    alpha = x + O(x^precision)
    a, e=get_isogeny(K,A,B,c,alpha, k,True, precision)
    get_parameters_size(a,e)
       
    end=datetime.now()
    print("End task", datetime.now().strftime("%H:%M:%S"), "\n")
    
    beta=get_beta(c, A, B, alpha)
    print("beta=", laurent_to_rational(beta)[2], "\n")

    psi = get_psi(c, A, B, alpha, beta, precision)
    print("psi=", psi, "\n", "\n", laurent_to_rational(psi)[2], "\n")

    if get_type_of_psi(psi) == -1:
        
        bound_period_psi = get_len(psi)
        
        if bound_period_psi > precision:
            precision = len_period_psi
            print("\n", "precision is now set to be at", bound_period_psi)
        else:
            print("\n", "precision not changed as the bound is", bound_period_psi)

        _,_,len_period_psi, _ = find_period_extended(psi, precision)
    
        l=test_compatibility(psi, k)
        print("\n", "There are", len(l), "compatible constant terms and hence at most", len(l), "rational isogenies." "\n")
        if len(l) > 0:
            gamma = get_gamma(A, precision, psi)
    
    
            _,_,len_period, _ = find_period_extended(gamma, precision)
    
            if len_period >= 0:
                print("\n", "For the above gamma we got that it is periodic, and we can write it in rational form.")
                print("\n", "gamma=", laurent_to_rational(gamma)[2], "\n")    

                for i in range(len(l)):
                    print(laurent_to_rational(e[0][i])[2], "is an isogeny", ver(laurent_to_rational(e[0][i])[2], c, GF(p^n)), "\n")
            else:
                print("Gamma is not periodic")
        else:
            print("The chosen parameters do not satisfy the compatibility conditions")
    else:
        str = get_type_of_psi(psi)
        l=test_compatibility(psi, k)
        print("Incompatible parameters, due to the fact that ", str, "\n")
        print("Also, there are", len(l), "compatible constant terms")
        
    print("We recovered a total number of", get_parameters_size(a,e)[1], "rational isogenies with this method in", end-start, "seconds")
    print("            ⣀⢀⣠⣤⣄⡀⢀⣀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠀⣠⡶⠛⢉⠤⣀⠤⡠⢫⠵⠶⢩⡢⠀⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⣀⠀⠀⠀⠀⠀⠀⢰⠋⠀⣠⢡⠋⠉⠙⣆⢂⣤⡄⠈⡇⡇⠀⠀⣀⣶⣄⢤⠀\n\
 ⢠⢇⠓⠒⣂⡤⡀⠀⡆⠀⡜⣿⣜⢄⣿⢆⠜⣤⣝⣓⣢⠜⠀⡠⢛⠧⠬⠭⠸⠇\n\
 ⠈⠒⠓⠂⠙⠓⢌⠢⢷⡫⠐⠉⠛⠴⠶⠖⠊⠀⠉⠉⠀⢸⠌⡰⠁⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠑⡀⠙⢕⢦⠀⠀⠠⣲⣒⠲⢲⠎⢻⢈⣷⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠸⡀⠀⢣⡑⡄⠀⠑⠠⠄⠘⠴⠂⣸⣹⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠃⠀⠀⢹⣼⡶⣄⠀⠀⠀⠀⡴⢿⢻⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⠀⠀⠀⡝⠁⠀⠙⠒⠒⠋⠀⢸⢸⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠀⢸⢄⣀⣀⡇⠀⠀⡖⢦⣴⠊⡆⢸⣸⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠀⢰⠀⠉⢸⠁⠀⠸⡇⣞⣯⡷⡇⢨⢹⠀⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠀⣸⡀⠔⠃⠀⠀⠀⠑⠬⠭⠝⠀⣈⡾⡄⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⡴⢣⠑⢄⣀⣀⣀⣀⣀⠀⠤⣐⢞⣿⡡⠃⠀⠀⠀⠀⠀⠀\n\
 ⠀⠀⠀⠀⠀⠀⠀⠀⠈⠁⠉⠉⠀⠀⠀⠀⠀⠀⠀⠈⠫⠙ ")

    

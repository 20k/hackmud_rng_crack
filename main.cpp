#include <iostream>
#include <z3++.h>
#include <z3.h>
#include <vector>
#include <math.h>
#include <stdint.h>

using namespace z3;

/*def sym_xs128p(slvr, sym_state0, sym_state1, generated):
    s1 = sym_state0
    s0 = sym_state1
    s1 ^= (s1 << 23)
    s1 ^= LShR(s1, 17)
    s1 ^= s0
    s1 ^= LShR(s0, 26)
    sym_state0 = sym_state1
    sym_state1 = s1
    calc = (sym_state0 + sym_state1)

    condition = Bool('c%d' % int(generated * random.random()))

    impl = Implies(condition, (calc & 0xFFFFFFFFFFFFF) == int(generated))

    slvr.add(impl)
    return sym_state0, sym_state1, [condition]*/


/*
    dubs = [0.71818029236637937, 0.13145321474034222, 0.22632317820137171]

    print dubs

    # from the doubles, generate known piece of the original uint64
    generated = []
    for idx in xrange(len(dubs)):
        recovered = struct.unpack('<Q', struct.pack('d', dubs[idx] + 1))[0] & 0xFFFFFFFFFFFFF
        generated.append(recovered)

    # setup symbolic state for xorshift128+
    ostate0, ostate1 = BitVecs('ostate0 ostate1', 64)
    sym_state0 = ostate0
    sym_state1 = ostate1
    slvr = Solver()
    conditions = []

    # run symbolic xorshift128+ algorithm for three iterations
    # using the recovered numbers as constraints
    for ea in xrange(len(dubs)):
        sym_state0, sym_state1, ret_conditions = sym_xs128p(slvr, sym_state0, sym_state1, generated[ea])
        conditions += ret_conditions

    print "built_conditions"

    if slvr.check(conditions) == sat:
        # get a solved state
        m = slvr.model()
        state0 = m[ostate0].as_long()
        state1 = m[ostate1].as_long()*/


double chrome_2(uint64_t v)
{
    uint64_t kExponentBits = uint64_t(0x3FF0000000000000);
    uint64_t kMantissaMask = uint64_t(0x000FFFFFFFFFFFFF);

    uint64_t random = ((v) & kMantissaMask) | kExponentBits;

    return (*(double*)&random) - 1;
}

double chrome(uint64_t v)
{
    uint64_t up = ((v & ((1ull << 52) - 1)) | 0x3FF0000000000000);

    return (*(double*)&up) -  1.0;
}

uint64_t iv_chrome(double v)
{
    uint64_t ret;

    double vn = v + 1.0;

    ret = *(uint64_t*)&vn;

    ///52 bits
    ret = ret & 0xFFFFFFFFFFFFF;

    return ret;
}

uint64_t state0 = 134125447415289812;
uint64_t state1 = 182415234512781923;
uint64_t xorshift128plus() {
    uint64_t s1 = state0;
    uint64_t s0 = state1;
    state0 = s0;
    s1 ^= s1 << 23;
    s1 ^= s1 >> 17;
    s1 ^= s0;
    s1 ^= s0 >> 26;
    state1 = s1;
    return state0 + state1;
}

/*for (ii = 0; ii < 32; ii += 1) {
  switch (ii) {
  case 8:
  case 20:
    uuid += '-';
    uuid += (Math.random() * 16 | 0).toString(16);
    break;
  case 12:
    uuid += '-';
    uuid += '4';
    break;
  case 16:
    uuid += '-';
    uuid += (Math.random() * 4 | 8).toString(16);
    break;
  default:
    uuid += (Math.random() * 16 | 0).toString(16);
  }*/

expr sym_round(expr& e1)
{
    auto t1 = e1.ctx().bv_val(1, 64);

    expr ret = to_expr(e1.ctx(), Z3_mk_bvudiv(e1.ctx(), e1, t1));

    return ret;
}

expr bv_to_double_assume_chrome(expr& e1)
{
    uint64_t mmask = 0xFFFFFFFFFFFFF; //52
    uint64_t eor = 0x3FF0000000000000; //dunno, exponent

    expr mantissa_mask = e1.ctx().bv_val((unsigned long long)mmask, 64);
    expr exponent_to_or = e1.ctx().bv_val((unsigned long long)eor, 64);

    expr res = (e1 & mantissa_mask) | exponent_to_or;

    expr dubd = to_expr(res.ctx(), Z3_mk_fpa_to_fp_bv(res.ctx(), res, Z3_mk_fpa_rounding_mode_sort(e1.ctx())));

    dubd = dubd - 1.0;

    return dubd;
}

void sym_xs128p(context& c, expr& sym_0, expr& sym_1, expr& sout0, expr& sout1, solver& s, const expr& t23, const expr& t17, const expr& t26, const expr& val, const expr& cpc)
{
    auto s1 = sym_0;
    auto s0 = sym_1;

    ///s1 ^= s1 << 23;
    s1 = s1 ^ to_expr(s1.ctx(), Z3_mk_bvshl(s1.ctx(), s1, t23));
    ///s1 ^= s1 >> 17
    s1 = s1 ^ to_expr(s1.ctx(), Z3_mk_bvlshr(s1.ctx(), s1, t17));

    ///s1 ^= s0
    s1 = s1 ^ s0;

    ///s1 ^= s0 >> 26
    s1 = s1 ^ to_expr(s1.ctx(), Z3_mk_bvlshr( s1.ctx(), s0, t26));

    sout0 = s0;
    sout1 = s1;

    expr calc = s0 + s1;

    s.add((calc & cpc) == val);
}

void sym_trust(expr& calc, expr& cpc)
{
    expr res = calc & cpc;

    ///double 0 -> 1
    expr rdb = bv_to_double_assume_chrome(res);
}


///Ok. I should be able to theorum solve if two states are compatible

void test()
{
    std::cout << "eval example 1\n";
    context c;
    expr x = c.int_const("x");
    expr y = c.int_const("y");
    solver s(c);

    /* assert x < y */
    s.add(x < y);
    /* assert x > 2 */
    s.add(x > 2);

    std::cout << s.check() << "\n";

    model m = s.get_model();
    std::cout << "Model:\n" << m << "\n";
    std::cout << "x+y = " << m.eval(x+y) << "\n";
}

int main()
{
    //test();

    //double dubs[] = {0.71818029236637937, 0.13145321474034222, 0.22632317820137171};

    //.39011942274229460814,0.54714196159077843618,0.86852546499401772628,0.13327812370798475250

    ///old confirmed to work
    //double dubs[] = {0.13327812370798475250, 0.86852546499401772628, 0.54714196159077843618};

    ///first "0.36086276216304247200, 0.16175621775668935776, 0.40025633058521936647, 0.52204290322396551538, 0.01685704548347843890, "
    ///second "0.95824843880028787169, 0.14979908670577679608, 0.63689794533182064740, 0.78247552460479963266, 0.18456434157936185692, "


    //double dubs[] = {0.01685704548347843890, 0.52204290322396551538, 0.40025633058521936647};

    //double check_array[] = {0.16175621775668935776, 0.36086276216304247200};

    //double dubs[] = {0.18456434157936185692, 0.78247552460479963266, 0.63689794533182064740};

    ///FIRST

    //0.99296038142003739679, 0.67136690702246015761, 0.69287991623370315253, 0.65795407859757215618, 0.07913877046405426441,

    //double dubs[] = {0.07913877046405426441, 0.65795407859757215618, 0.69287991623370315253};

    //0.54617820951415607666 0.89771194842165646932 0.72121940866315736862
    //double dubs[] = {0.72121940866315736862, 0.89771194842165646932, 0.54617820951415607666};

    //0.07706014015747708612 0.80691492856844981851 0.78186155401088353045
    ///javascript rng produces values backwards, you must reverse the output order of values into this array
    //double dubs[] = {0.78186155401088353045, 0.80691492856844981851, 0.07706014015747708612};

    //double dubs[] = {0.7330763544427232,0.6669781536352002,0.8730758728865933};

    //double check_array[] = {0.14979908670577679608, 0.95824843880028787169};

    ///stranger danger
    ////wait. these were produced earlier right?
    //double predict_array[] = {0.18456434157936185692};

    //double predict_array[] = {0.36086276216304247200};

    //double dubs[] = {0.3411049510649453, 0.7330763544427232,0.6669781536352002};


    ///0.87680113501854894942 0.52770718623711920792 0.23358886399449940718 0.43543085194042063790 0.63940280107389257935

    double dubs[] = {0.63940280107389257935, 0.43543085194042063790, 0.23358886399449940718};


    int ndubs = sizeof(dubs) / sizeof(double);

    config cfg;

    z3::context c(cfg);

    expr s0 = c.bv_const("ostate0", 64);
    expr s1 = c.bv_const("ostate1", 64);

    auto s0b = s0;
    auto s1b = s1;

    auto t23 = c.bv_val(23, 64);
    auto t17 = c.bv_val(17, 64);
    auto t26 = c.bv_val(26, 64);

    uint64_t cp = 0xFFFFFFFFFFFFF;

    expr cpc = c.bv_val((unsigned long long)cp, 64);

    std::vector<uint64_t> converted;

    for(int i=0; i<ndubs; i++)
    {
        converted.push_back(iv_chrome(dubs[i]));

        //printf("%f\n", chrome(converted.back()));
    }

    printf("%i nd\n", ndubs);

    std::vector<expr> cond;

    solver s(c);

    for(int i=0; i<ndubs; i++)
    {
        auto e2 = c.bv_val((unsigned long long)converted[i], 64);

        if(i % 2 == 1)
            sym_xs128p(c, s0b, s1b, s0, s1, s, t23, t17, t26, e2, cpc);
        else
            sym_xs128p(c, s0, s1, s0b, s1b, s, t23, t17, t26, e2, cpc);


        std::cout << converted[i] << std::endl;
    }

    /*auto e2 = c.bv_val((unsigned long long)converted[0], 64);

    sym_xs128p_sim(c, s0b, s1b, s0, s1, s, t23, t17, t26, e2, converted[0], cpc);

    std::cout << s0.simplify() << std::endl;
    std::cout << s1.simplify() << std::endl;

    sym_xs128p(c, s0b, s1b, s0, s1, s, t23, t17, t26, e2, converted[0], cpc);

    std::cout << s0.simplify() << std::endl;
    std::cout << s1.simplify() << std::endl;

    return 0;*/


    check_result res = s.check();

    //std::cout << s << std::endl;

    if(res == check_result::sat)
    {
        printf("yay\n");

        model m = s.get_model();

        func_decl d0 = m.get_const_decl(0);
        func_decl d1 = m.get_const_decl(1);

        expr e1 = m.get_const_interp(d0);
        expr e2 = m.get_const_interp(d1);

        uint64_t s0;// = e1;
        uint64_t s1;// = e2;

        Z3_get_numeral_uint64(c, e1, &s0);
        Z3_get_numeral_uint64(c, e2, &s1);

        std::cout << m << std::endl;

        std::cout << d0 << std::endl;
        std::cout << d1 << std::endl;

        std::cout << e1 << std::endl;
        std::cout << e2 << std::endl;

        std::cout << s0 << std::endl;
        std::cout << s1 << std::endl;

        std::cout << std::hex << s0 << std::endl;
        std::cout << std::hex << s1 << std::endl;

        state0 = s0;
        state1 = s1;

        std::cout.precision(20);

        for(int i=0; i<5; i++)
        {
            uint64_t res = xorshift128plus();

            double d = chrome(res);

            std::cout << d << std::endl;
        }

        for(int i=0; i<0; i++)
        {
            uint64_t res = xorshift128plus();

            double d = chrome(res);

            //bool is_eq = d == check_array[i];

            //std::cout << "ie " << is_eq << " num " << d << std::endl;
        }

        /*bool found = false;

        for(int i=0; i<100000000; i++)
        {
            uint64_t res = xorshift128plus();

            double d = chrome(res);

            //std::cout << "n " << d << " s " << predict_array[0] << std::endl;

            if(d == predict_array[0])
            {
                printf("we're good\n");

                found = true;
            }
        }

        if(!found)
        {
            printf("fuck\n");
        }*/

    }
    else
    {
        printf("UNSAT\n");

        //std::cout << s << std::endl;
    }

    //f1 101110001100001100000010111111000000010011000100101
    //f2 101110001100001100000001000000111010101101000010110

    return 0;
}

const BigInteger = require('big-integer'),
      {sha3_256} = require('js-sha3');
class ModularMath
{
    static inverse(a, p)
    {
        let t = BigInteger(0),
            new_t = BigInteger(1),
            r = p,
            new_r = a,
            quotient = BigInteger(0),
            tmp = BigInteger(0);
        while (new_r.notEquals(BigInteger(0)))
        {
            quotient = r.divide(new_r);
            tmp = new_t;
            new_t = t.minus(quotient.multiply(new_t));
            t = tmp;
            tmp = new_r;
            new_r = r.minus(quotient.multiply(new_r));
            r = tmp;
        }
        if (r.greater(BigInteger(1))) throw EvalError("Element has no inverse element!");
        if (t.lesser(BigInteger(0))) t = t.plus(p);
        return t;
    }
    static nearest(a, p)
    {
        if (a.greaterOrEquals(BigInteger(0))) return a;
        a = a.plus(a.divide(p).abs());
        if (!a.isZero()) a = a.plus(p);
        return a;
    }
}
class Point
{
    constructor(x, y, a, b, p)
    {
        x = BigInteger(x);
        y = BigInteger(y);
        a = BigInteger(a);
        b = BigInteger(b);
        p = BigInteger(p);
        if (p.lesserOrEquals(BigInteger(3)))
            throw RangeError("Finite field parameter must be greater than 3 for cryptographical purposes!");
        this.#x = x;
        this.#y = y;
        this.#a = a;
        this.#b = b;
        this.#p = p;
    }
    get x()
    {
        return this.#x;
    }
    get y()
    {
        return this.#y;
    }
    get a()
    {
        return this.#a;
    }
    get b()
    {
        return this.#b;
    }
    get p()
    {
        return this.#p;
    }
    add(another_point)
    {
        if (this.#a.notEquals(another_point.a) || this.#b.notEquals(another_point.b))
            throw TypeError("Elliptic curve parameters of the points are not equal!");
        if (this.#p.notEquals(another_point.p))
            throw TypeError("Finite field parameters of the points are not equal!");
        if (this.#x === Infinity || another_point.x === Infinity)
            throw RangeError("Coordinate x must not be infinity!");
        if ((this.#x.equals(another_point.x) && this.#y.equals(another_point.y) &&
            this.#y === Infinity) || this.#y === Infinity) return new Point(this.#x, this.#y,
           this.#a, this.#b, this.#p);
        if (this.#x.equals(another_point.x) && this.#y.equals(another_point.y))
            return this.#double_multiply();
        if (this.#x.equals(another_point.x) && this.#y.equals(another_point.y.multiply(BigInteger(-1))))
            return new Point(this.#x, Infinity, this.#a, this.#b, this.#p);
        return this.#add_different(another_point);
    }
    multiply(entered_multiplier)
    {
        let multiplier = BigInteger(entered_multiplier);
        if (multiplier.isNegative())
        {
            let new_point = new Point(this.#x, this.#y.multiply(BigInteger(-1)), this.#a, this.#b, this.#p);
            return new_point.multiply(multiplier.abs());
        }
        if (multiplier.isZero()) return new Point(this.#x, Infinity, this.#a, this.#b, this.#p);
        if (multiplier.equals(BigInteger(1))) return new Point(this.#x, this.#y, this.#a, this.#b, this.#p);
        if (multiplier.equals(BigInteger(2))) return this.#double_multiply();
        multiplier = multiplier.toString(2);
        let length = multiplier.length;
        let degrees = [];
        for (let i = length - 1; i >= 0; --i)
            if (multiplier.charAt(length - i - 1) === '1')
                degrees.push(BigInteger(2).pow(i));
        let new_point, degree, iteration_point;
        length = degrees.length;
        degree = BigInteger(degrees.at(0));
        iteration_point = new Point(this.#x, this.#y, this.#a, this.#b, this.#p);
        while (degree.notEquals(BigInteger(1)))
        {
            iteration_point = iteration_point.#double_multiply();
            degree = degree.divide(BigInteger(2));
        }
        new_point = iteration_point;
        for (let i = 1; i < length; ++i)
        {
            degree = BigInteger(degrees.at(i));
            iteration_point = new Point(this.#x, this.#y, this.#a, this.#b, this.#p);
            while (degree.notEquals(BigInteger(1)))
            {
                iteration_point = iteration_point.#double_multiply();
                degree = degree.divide(BigInteger(2));
            }
            new_point = new_point.add(iteration_point);
        }
        return new_point;
    }
    #add_different(another_point)
    {
        let lambda;
        let numerator = another_point.y.minus(this.#y);
        let denominator = another_point.x.minus(this.#x);
        let modular_division = numerator.divmod(denominator);
        if (modular_division.remainder.equals(BigInteger(0)))
            lambda  = modular_division.quotient;
        else
        {
            let GCD = BigInteger.gcd(numerator, denominator);
            let multiplying = numerator.multiply(denominator);
            let sign = multiplying.isPositive() ? BigInteger(1) : BigInteger(-1);
            numerator = numerator.abs().divide(GCD);
            denominator = ModularMath.inverse(denominator.abs().divide(GCD), this.#p);
            multiplying = numerator.multiply(denominator).multiply(sign);
            if (multiplying.isNegative()) multiplying = ModularMath.nearest(multiplying, this.#p);
            lambda = multiplying;
        }
        let new_x = lambda.pow(BigInteger(2)).minus(this.#x).minus(another_point.x).mod(this.#p),
            new_y = lambda.multiply(this.#x.minus(new_x)).minus(this.#y).mod(this.#p);
        new_x = ModularMath.nearest(new_x, this.#p);
        new_y = ModularMath.nearest(new_y, this.#p);
        return new Point(new_x, new_y, this.#a, this.#b, this.#p);
    }
    #double_multiply()
    {
        if (this.#y.isZero()) return new Point(this.#x, this.#y, this.#p);
        let lambda;
        let numerator = this.#x.pow(BigInteger(2)).multiply(BigInteger(3)).plus(this.#a);
        let denominator = this.#y.multiply(BigInteger(2));
        let modular_division = numerator.divmod(denominator);
        if (modular_division.remainder.isZero())
            lambda  = modular_division.quotient;
        else
        {
            let GCD = BigInteger.gcd(numerator, denominator);
            let multiplying = numerator.multiply(denominator);
            let sign = multiplying.isPositive() ? BigInteger(1) : BigInteger(-1);
            numerator = numerator.abs().divide(GCD);
            denominator = ModularMath.inverse(denominator.abs().divide(GCD), this.#p);
            multiplying = numerator.multiply(denominator).multiply(sign);
            multiplying = ModularMath.nearest(multiplying, this.#p);
            lambda = multiplying;
        }
        let new_x = lambda.pow(BigInteger(2)).minus(this.#x.multiply(BigInteger(2))).mod(this.#p),
            new_y = lambda.multiply(this.#x.minus(new_x)).minus(this.#y).mod(this.#p);
        new_x = ModularMath.nearest(new_x, this.#p);
        new_y = ModularMath.nearest(new_y, this.#p);
        return new Point(new_x, new_y, this.#a, this.#b, this.#p);
    }
    #x = BigInteger(0);
    #y = BigInteger(0);
    #a = BigInteger(0);
    #b = BigInteger(0);
    #p = BigInteger(0);
}
function generate_secp256k1_keys()
{
    let check = false;
    const n = BigInteger('fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141', 16);
    let G = new Point(BigInteger('79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798', 16),
        BigInteger('483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8', 16),
        BigInteger(0),
        BigInteger(7),
        BigInteger('fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f', 16));
    let d = BigInteger.randBetween(BigInteger(1), BigInteger(n, 16).minus(BigInteger(1)));
    let Q, private_key, public_key;
    while (!check)
    {
    try
    {
    Q = G.multiply(d);
    check = Q.x.lesserOrEquals(Q.p) && Q.y.lesserOrEquals(Q.p) &&
        Q.y.multiply(Q.y)
            .minus(Q.x.multiply(Q.x).multiply(Q.x))
            .minus(BigInteger(7))
            .mod(Q.p).isZero();
    }
    catch(infinite_error)
    {
        check = false;
    }
    try
    {
        Q.multiply(n);
        check = false;
    }
    catch(infinite_error)
    {
        private_key = d;
        public_key = {Q, G, n};
    }
    }
    return {private_key, public_key};
}
function sign(data, private_key, public_key)
{
    let check = false;
    let r, s;
    while (!check)
    {
    let k = BigInteger.randBetween(BigInteger(1), BigInteger(public_key.n, 16).minus(BigInteger(1)));
    let M = public_key.G.multiply(k);
    r = M.x.mod(public_key.n);
    check = !r.isZero();
    let inverse_k = ModularMath.inverse(k, public_key.n);
    let message_hash = BigInteger(sha3_256(data), 16);
    s = inverse_k.multiply(message_hash.plus(private_key.multiply(r))).mod(public_key.n);
    check = !s.isZero();
    }
    return {r, s};
}
function verify(data, public_key, r, s)
{
    if (r.lesser(BigInteger(1)) || r.greaterOrEquals(public_key.n) ||
        s.lesser(BigInteger(1)) || s.greaterOrEquals(public_key.n)) return false;
    let w = ModularMath.inverse(s, public_key.n);
    let message_hash = BigInteger(sha3_256(data), 16);
    let u1 = message_hash.multiply(w).mod(public_key.n);
    let u2 = r.multiply(w).mod(public_key.n);
    let M = public_key.G.multiply(u1).add(public_key.Q.multiply(u2));
    let v = M.x.mod(public_key.n);
    return v.equals(r);
}
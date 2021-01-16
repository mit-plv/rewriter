set datafile separator ",";
set print "UnderLetsPlus0.txt-fits.dat";





f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'UnderLetsPlus0.txt' u 1:11 via a,b,c;
print "Rewrite-lhs-for-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;














f(x) = a*exp(b*x);
a=1;
b=1;
fit f(x) 'UnderLetsPlus0.txt' u 1:50 via a,b;
print "rewrite-strat(bottomup)-regression-exponential: ", a, "*Qexp(", b, "*x)";


f(x) = a*exp(b*x);
a=1;
b=1;
fit f(x) 'UnderLetsPlus0.txt' u 1:53 via a,b;
print "rewrite-strat(topdown)-regression-exponential: ", a, "*Qexp(", b, "*x)";



f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'UnderLetsPlus0.txt' u 1:59 via a,b,c,d;
print "setoid-rewrite-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;



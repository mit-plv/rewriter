set datafile separator ",";
set print "Plus0Tree.txt-fits.dat";





f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'Plus0Tree.txt' u 1:16 via a,b,c;
print "Rewrite-lhs-for-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;


f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'Plus0Tree.txt' u 1:19 via a,b,c,d;
print "autorewrite-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;














f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'Plus0Tree.txt' u 1:58 via a,b,c,d;
print "rewrite!-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;


f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'Plus0Tree.txt' u 1:61 via a,b,c,d;
print "rewrite-strat(bottomup)-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;


f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'Plus0Tree.txt' u 1:64 via a,b,c,d;
print "rewrite-strat(topdown)-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;



f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'Plus0Tree.txt' u 1:70 via a,b,c,d;
print "setoid-rewrite-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;


f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'Plus0Tree.txt' u 1:73 via a,b,c,d;
print "ssr-rewrite!-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;



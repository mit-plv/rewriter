set datafile separator ",";
set print "SieveOfEratosthenes.txt-fits.dat";





f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:11 via a,b,c;
print "Rewrite-lhs-for-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;


f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:14 via a,b,c,d;
print "cbn-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;


f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:17 via a,b,c;
print "cbv-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;








f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:38 via a,b,c;
print "lazy-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;






f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:45 via a,b,c;
print "native-compute(1)-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;






f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:52 via a,b,c;
print "native-compute(2)-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;









f(x) = a*x**3+b*x**2+c*x+d;
a=1;
b=1;
c=1;
d=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:76 via a,b,c,d;
print "simpl-regression-cubic: ", a, "*x^3", "+", b, "*x^2", "+", c, "*x", "+", d;


f(x) = a*x**2+b*x+c;
a=1;
b=1;
c=1;
fit f(x) 'SieveOfEratosthenes.txt' u 1:79 via a,b,c;
print "vm-compute-regression-quadratic: ", a, "*x^2", "+", b, "*x", "+", c;



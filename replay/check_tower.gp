\\ Exact field check for s^2=2, r^2=s-1/2, i^2=-1, Phi_7(zeta)=0.
\\ Eliminating s gives 4*r^4+4*r^2-7; conversely s=r^2+1/2.
f=4*x^4+4*x^2-7;
if(!polisirreducible(f),error("quartic field is reducible"));
c8=polcompositum(f,x^2+1);
if(#c8!=1 || poldegree(c8[1])!=8 || !polisirreducible(c8[1]),error("degree-eight compositum failed"));
c48=polcompositum(c8[1],polcyclo(7));
if(#c48!=1 || poldegree(c48[1])!=48 || !polisirreducible(c48[1]),error("degree-forty-eight compositum failed"));
print("TOWER_DEGREES=[4,8,48]");
print("TOWER_IRREDUCIBLE=1");
quit;

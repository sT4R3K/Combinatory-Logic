# Combinatory-Logic
## ([Mr's Dominique Larchey-Wendling Project](https://github.com/DmxLarchey/Combinatory-Logic-for-students))

Usage:
```
make all
coqide *.v & 
```
dependencies:
```
tacs.v		:
rel.v		: tacs.v
square.v        : tacs.v rel.v
cl.v		:
cl_eq.v		: cl.v
cl_confluent.v	: rel.v square.v cl.v
cl_beta.v	: tacs.v rel.v square.v cl.v cl_eq.v cl_confluent.v
cl_beta_inv.v	: cl.v cl_eq.v cl_beta.v
cl_normal.v  	: rel.v cl.v cl_eq.v cl_beta.v cl_beta_inv.v
cl_beta_redex.v	: rel.v cl.v cl_eq.v cl_beta.v cl_beta_inv.v cl_normal.v
```

= Cauchy Integral Package

This Mathematica package calculates arbitrary derivative of a holomorphic function by evaluating a Cauchy integral. The contour of this integral is automatically chosen such that it yields a small condition number for the integral and consequently also accurate results for the derivative.

== Example
The following code yields the 20-th derivative of the exponential function at z = 0
```Mathematica
CauchyIntegralD[Exp,20,0]
```

== Further Information
Please see the [Readme.nb](https://github.com/tauu/CauchyIntegral/raw/Readme.nb) notebook for further details and examples.

== References
[Optimal Contours for High-Order Derivatives](http://arxiv.org/abs/1107.0498)
[Accuracy and Stability of Computing High-Order Derivatives of Analytic Functions by Cauchy Integrals](https://arxiv.org/abs/0910.1841)

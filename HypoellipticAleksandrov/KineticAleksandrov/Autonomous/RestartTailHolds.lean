module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartDensity

/-! # Provider for the restarted one-pole density tail

Source: companion paper, Corollary 8.4 (survival and restarted-tail estimates).

This module proves `restartTailStatement_holds`, the restarted-tail estimate. The
statement quantifies over the Hörmander hypoellipticity theorem and classical
Dirichlet solvability for ellipsoids (Lieberman, Theorem 5.14). Its constants precede the
coefficient, clock and starting pole, and one density works for every delay.
-/

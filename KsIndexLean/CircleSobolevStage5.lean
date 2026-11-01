module

public import KsIndexLean.BoundaryArcClosure
public import KsIndexLean.CircleSobolevClosed
public import KsIndexLean.CircleSobolevHomogeneous

@[expose] public section


/-!
Public entry point for real-order weighted Fourier circle Sobolev spaces,
physical L² realization, conjugate-first duality, rotations and character spaces,
bounded DtN symbol, Fourier approximation, compact inclusion, and the weak disk
trace with its exact supported-arc interpretation.

Negative orders use weighted coefficient sequences, not an L² subspace.
The DtN coefficient identification does not by itself transfer coefficient
diagonal-form index/nullity theorems to this Hilbert domain.
-/

module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.ToHLat
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareMomentFromBound
public import Formalism.GL3MeanSquares.ConcavityEquidistribution
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareMomentArithmeticBound

@[expose] public section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def formAt {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (P : V →ₗ⋆[K] V →ₗ[K] K)
    (v : InfinitePlace K) (x y : V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (b.repr x i)) * v.embedding (P (b i) (b j)) * v.embedding (b.repr y j)

end Forms

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

end Std

section Nums

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

end Nums

section Named

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable (K) {n : ℕ}

end Named

section NamedCol

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end NamedCol

section Main

end Main

section PartI

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

variable (hX : X.Ok)

end PartI

end Formalism.L2.Col

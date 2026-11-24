module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedVectorLiftStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionFixedSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictlyDominantHeckeKernelStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem c3 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C3 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ
  exact ⟨GlobalTheory.T.jacquet_projection_fixed_surjective k N h d hd J hJo hJc hJf hpos V π hπ.1,
    GlobalTheory.T.jacquet_fixed_vector_lift k N h d hd J hJo hJc hJf hpos V π hπ,
    GlobalTheory.T.strictly_dominant_hecke_kernel k N h d hd J hJo hJc hJf hpos V π hπ.1⟩

end GlobalTheory.CompanionTheory.Lbc

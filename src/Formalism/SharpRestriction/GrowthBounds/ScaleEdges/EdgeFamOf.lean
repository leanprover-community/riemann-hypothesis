module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeMulOfWeightSum
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def EdgeFamOf : Prop :=
  ∀ (D : Formalism.BasicNotions.D7), tableLineDegreeFive.LevelPrimesProviso D → BePerfect → DualHeightInclusion →
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
  ∀ (m r : ℕ) (fl rest lam0 : Fin n' → Fin (m + 1) → ℤ) (hnu : lam0 = fl + rest) (h1 : IsDominant fl)
    (h2 : IsDominant rest) (e : Edge W Qq (m + 1)), IsEdge p n' r e →
  ∀ (nb n2 T oS tT D1 cStar c' : ℕ), cStar + oS ≤ c' → 2 * (D1 + 1) ≤ c' →
  ∀ (Fvb Sy : Fin nb → Vsp Kf fl) (sh : Fin n2 → Vsp Kf rest),
    (∀ b, Fvb b ∈ scale (algebraMap O Kf w ^ (-(T : ℤ))) (HL (O := O) ι σ fl e.src)) →
    (∀ b, Fvb b - Sy b ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r fl e)) →
    (∀ b, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = e.src → e' ≠ e →
      Fvb b ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r fl e')) →
    (∀ b, Sy b ∈ Re p ι σ w r fl e) →
    (∀ i, sh i ∈ Re p ι σ w r rest e ∧
      sh i ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (HL (O := O) ι σ rest e.src)) →
    (∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
      ∃ G : Module.Dual Kf (Vsp Kf lam0),
        G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
        G ∈ Re' p ι σ w r lam0 e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
        ValLe (p : O) D1 (be p r lam0 (∑ x, c x • mulV hnu h1 h2 (Sy x.1) (sh x.2)) G)) →
    EdgeFam (W := W) (O := O) p n' ι σ w r lam0 (T + oS) tT D1 cStar e (nb * n2)

end Formalism.MainNotions.Pf14

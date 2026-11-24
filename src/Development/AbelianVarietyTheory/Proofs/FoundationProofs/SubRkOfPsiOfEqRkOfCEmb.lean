module

public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

def trivialIntersectionTheory (d : ℕ) : DV.ITh where
  LB := Unit
  Ch := ℚ
  c1 := fun _ => 0
  VDiv := ℚ
  cD := 0
  capDeg := 0
  divP := 1
  cD_divP := rfl
  dim := d

def trivialFlagPair (d r : ℕ) : DV.FPair (trivialIntersectionTheory d) r where
  x := fun _ => ()
  x' := fun _ => ()
  Dv := fun _ => 0
  hx := fun _ => by
    rw [map_zero, sub_zero]

theorem sub_rkOf_psiOf_eq_rkOf_cEmb (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) (τ : DV.Emb D p) :
    N - DV.rkOf (DV.PsiOf D jc) N j τ = DV.rkOf (DV.PsiOf D jc) N j (DV.cEmb D τ) := by
  have h := Formalism.L2.Geo.cm_type_meets_conjugate_pair p jc τ
  unfold DV.rkOf
  by_cases hτ : τ ∈ DV.PsiOf D jc
  · rw [if_pos hτ, if_neg (h.1 hτ)]
  · have hc : DV.cEmb D τ ∈ DV.PsiOf D jc := by
      by_contra hn
      exact hτ (h.2 hn)
    rw [if_neg hτ, if_pos hc]
    omega

def trivialAdmissibleModel (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := trivialIntersectionTheory (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
  cov := 1
  cov_pos := Nat.one_pos
  lvl := 0
  lie := fun _ => trivialFlagPair _ _
  om := fun _ => trivialFlagPair _ _
  lieW := trivialFlagPair _ _
  omW := trivialFlagPair _ _
  om_dual := fun τ =>
    ⟨finCongr (sub_rkOf_psiOf_eq_rkOf_cEmb D p jc N j hj τ), fun _ => neg_zero.symm⟩
  dim_eq := rfl
  omW_dual := ⟨Equiv.refl _, fun _ => neg_zero.symm⟩

theorem nonempty_admissibleModel :
    ∀ (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (N j : ℕ), j ≤ N →
      Nonempty (DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j)) :=
  fun D p _ jc N j hj => ⟨trivialAdmissibleModel D p jc N j hj⟩

end GlobalTheory

end

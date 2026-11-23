module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open ProjSpace

theorem IsAmpleLB.exists_affine_boundary_functions {Y : Scheme.{0}} {L : LB Y} (h : IsAmpleLB L) (U : Y.Opens)
    (x : Y) (hx : x ∈ U) : ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
      ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
        resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  obtain ⟨k, hk, hg⟩ := h.exists_isGenerated_pow
  obtain ⟨d, -, t, hxt, hle, ha⟩ := ((isAmpleLB_pow_iff h.isLB hk).2 h).exists_affine_le hx
  obtain ⟨n, s, hs⟩ := hg.pow d
  refine ⟨nonzeroLocus t, n, fun l => secRatio t (s l), hxt, hle, ha, fun z => ?_⟩
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  refine ⟨nonzeroLocus (s l), secRatio (s l) t, l, hl, basicOpen_secRatio _ _, ?_⟩
  rw [secRatio_mul_secRatio t (s l) t inf_le_right inf_le_left, secRatio_self, map_one]

theorem exists_affine_boundary_functions_of_isProjOver :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (U : Y.Opens) (x : Y), x ∈ U →
      ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
        ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
          resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  rintro Y p ⟨N, i, hi, -⟩ U x hx
  exact ((isAmple_projective_O_one ℂ N).pull_of_isAffineHom i).exists_affine_boundary_functions U x hx

end GlobalTheory

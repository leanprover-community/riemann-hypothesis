module

public import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Formalism.LocalToGlobal.Columns.RecLevelLocF
import Formalism.LocalToGlobal.Columns.RecLevelLocK
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneAtT

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem th_fLoc_pi (h : BasePi ST π) (a : Formalism.BasicNotions.intV E v)
    (ha : (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π)) (m : fMod hc n ST v) :
    a • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  show a • fLoc hc n ST v x = 0
  rw [← map_smul, rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star (algebraMap (𝓞 E) E π))) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  refine ⟨fun i hi => mul_mem a.2 (hx.1 i hi), ?_⟩
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π) / algebraMap (𝓞 E) E π) *
    ((a : E ⊗[F] v.adicCompletion F) * x.1 (lastIdx n)) ∈ Formalism.BasicNotions.intV E v
  rw [ha, rll_cp_mul v h]
  exact hx.2

end Loc

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

end Gen

end Formalism.L2.Col

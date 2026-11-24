module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix

namespace Formalism.L2.SG.TermOp

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem one_mem_isom : (1 : S.V ≃ₗ[E] S.V) ∈ Formalism.HermitianLatticesTheory.isom S.hT := (Formalism.HermitianLatticesTheory.isom S.hT).one_mem

theorem mapFlag_one (F : FlagG S r T) : mapFlag 1 one_mem_isom F = F := by
  rfl

theorem mapLF_one (F : LFlag S r T) : mapLF 1 F = F := by
  unfold mapLF
  rw [dite_eq_left one_mem_isom, mapFlag_one]
  rfl

end Flag

section Id

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ratLink_one : RatLink X 1 1 := by
  refine ⟨1, (Formalism.UG.UJ _ _).one_mem, ?_, by simp, ?_⟩
  · intro v
    simpa [uMat] using (Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul _ v).symm
  · intro y
    simp

variable {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def idGTerm (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) (hrow : IsRowLat D F0 Λ) :
    GTerm X u u F0 F0 what₂ what₂ :=
  ⟨Λ, hΛ, Λ, hΛ, Quot.mk _ ⟨((1 : X.B.I.GA), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V)),
    ratLink_one X, one_mem_isom, by
      unfold Formalism.HermitianLatticesTheory.gmap
      simp,
    by
      rw [mapLF_one]
      exact TermDef.pd_self F0 Λ hrow⟩⟩

end Id

section Gam

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem gamma_one_pos : 0 < Gam1 TR := by
  unfold Gam1 Formalism.L2.SG.GGMirabolic.gamProd
  simp only [Pi.one_apply, Formalism.L2.SG.GGMirabolic.gam_one]
  have hprod : (∏ v, ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℂ) /
      (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℂ))) =
      ((∏ v, ((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, Complex.ofReal_re]
  apply Finset.prod_pos
  intro v _
  apply div_pos
  · exact_mod_cast Fintype.card_pos
  · have hU : 0 < Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k := by
      unfold Formalism.L2.SG.GGMirabolic.cardU
      refine Nat.card_pos_iff.mpr ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
      refine ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne (ne_of_lt hij).symm]⟩
    exact_mod_cast hU

end Gam

end Formalism.L2.SG.TermOp

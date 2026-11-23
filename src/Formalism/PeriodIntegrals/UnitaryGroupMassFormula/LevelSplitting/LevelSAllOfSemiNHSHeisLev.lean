module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCIface
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.CoordinateHomeomorphism
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} [FiniteDimensional F E]

theorem isClosed_FixXp {r : ℕ} (P : Frame E M r) :
    IsClosed (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have h : (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) =
      ⋂ v, ⋂ (_ : InXperp (Af F) σ J P v), {g | lin (Af F) σ J g v = v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (ExC.continuous_lin _) continuous_const

theorem ncoord_of_parts (hH : HeisP F E σ M J) (hL : LevP F E σ M J) : NCoord F E σ M J := by
  intro hJ hinv r P T hP
  obtain ⟨sH, csH, cyH, hs1, hdec, hyH, hZN1, hcent, hmul, hZnorm, hconj, hZconj⟩ :=
    hH hJ hinv r P T hP
  obtain ⟨A, Lev, hAN, hAcl, cLev, hLev, hAN1, hN1norm, hAcomm⟩ := hL hJ hinv r P T hP
  have hmemW : ∀ m : LevelUnipotentSubgroup (Af F) σ J P, ∀ a, yH (Af F) σ J P m a ∈ Wp (Af F) σ J P := by
    intro m a
    obtain ⟨y, hy, -⟩ := hdec m m.2
    rw [← hy a]; exact (y a).2
  let yQ : LevelUnipotentSubgroup (Af F) σ J P → (Fin r → Wp (Af F) σ J P) := fun m a =>
    ⟨yH (Af F) σ J P m a, hmemW m a⟩
  have H : CoordHyp (Nsub (Af F) σ J P) A (LevelUnipotentSubgroup (Af F) σ J P) (Zsub (Af F) σ J P) Lev sH yQ :=
    { hAN := hAN
      coordinate_level_le := inf_le_left
      hZN1 := hZN1
      cLev := cLev
      csH := csH
      cyQ := continuous_pi fun a => Continuous.subtype_mk
        ((continuous_apply a).comp (cyH.comp continuous_subtype_val)) _
      lev_mem := fun n hn => (hLev n hn).1
      lev_rest := fun n hn => (hLev n hn).2
      triv := hAN1
      norm1 := hN1norm
      sH_mem := hs1
      dec := fun m => by
        obtain ⟨y, hy, hz⟩ := hdec m m.2
        have : yQ m = y := funext fun a => Subtype.ext (hy a).symm
        rw [this]; exact hz
      yQ_sH := fun y z hz => funext fun a => Subtype.ext (hyH y z hz a)
      cent := hcent
      mul := hmul }
  refine ⟨A, Zsub (Af F) σ J P, cHomeo H, hAcl, ?_, fun n0 => coord_skew H n0, ?_⟩
  · show IsClosed ((Nsub (Af F) σ J P ⊓ FixXp (Af F) σ J P : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J))
    rw [Subgroup.coe_inf]
    exact (ExC.isClosed_Nsub hJ hinv P T hP).inter (isClosed_FixXp P)
  · intro h hh u y z
    obtain ⟨y', hy', hc⟩ := hconj h hh y
    refine ⟨y', hy', ?_⟩
    rw [cHomeo_apply, cHomeo_apply]
    have hu : h * (u : HA (Af F) σ J) * h⁻¹ = u := by rw [hAcomm h hh u u.2]; group
    have hz : h * (z : HA (Af F) σ J) * h⁻¹ = z := hZconj h hh z z.2
    calc h * ((u : HA (Af F) σ J) * sH y * (z : HA (Af F) σ J)) * h⁻¹
        = (h * u * h⁻¹) * (h * sH y * h⁻¹) * (h * z * h⁻¹) := by group
      _ = u * sH y' * z := by rw [hu, hc, hz]

end Ext

theorem ncoordAll_of (hH : HeisPAll) (hL : LevPAll) : NCoordAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact ncoord_of_parts (hH F E σ hσ M J hJ) (hL F E σ hσ M J hJ)

theorem levelSAll_of_semiNHS_heis_lev (hS : PI.LevelKSplit.W.ExS.SemiNHSAll) (hH : HeisPAll) (hL : LevPAll)
    (hV : PI.LevelKSplit.W.CD.ModVAll) (hA : NCAsmAll) : PI.LevelKSplit.LevelSAll :=
  levelSAll_of_parts hS (ncoordAll_of hH hL) hV hA

end PI.LevelKSplit.W.NC

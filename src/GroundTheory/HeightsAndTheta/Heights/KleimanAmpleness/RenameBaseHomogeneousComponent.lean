module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerRest
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestFurther
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XNotMemMIdealOver
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

section

variable {k : Type} [Field k] {N m : ℕ}

theorem weight_mapDomain_base (e : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (graphIdx N m))
        (Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e) =
      Sum.elim (fun _ => e.degree) (fun _ => 0) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  funext c
  rw [← sum_block_eq_blockWeight]
  rcases c with ⟨⟩ | ⟨⟩
  · simp only [Sum.elim_inl]
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl fun a _ => Finsupp.mapDomain_apply_of_injective hinj e a
  · simp only [Sum.elim_inr]
    refine Finset.sum_eq_zero fun b _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨a, ha⟩
    cases (Sigma.mk.inj ha).1

theorem rename_base_homogeneousComponent (d : ℕ) (f : Kleiman.Poly k N) :
    rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (homogeneousComponent d f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) (Sum.elim (fun _ => d) (fun _ => 0))
        (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj, coeff_homogeneousComponent,
      weight_mapDomain_base]
    by_cases hd : e.degree = d
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (congrFun h (Sum.inl ()))]
  · push Not at he
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

end

theorem CurveComap.proof (hR : SectionRatio.Statement) (hD : RatioDim.Statement) : CurveComap.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle e
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
  have hdim := hD k N m W hW.isPrime hW.multiHomog j hj fun b => by
    obtain ⟨d, f, g, -, -, h1, h2⟩ := hR k N Ω x Q n m s hx hgen W hW hle j b hj
    exact ⟨f, g, h1, h2⟩
  have hsub : Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) e ↔
      ringKrullDim (Kleiman.Poly k N ⧸
          W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) =
        ((e + 1 : ℕ) : WithBot ℕ∞) := by
    refine ⟨fun h => h.dim, fun h => ⟨Ideal.comap_isPrime _ _, fun f hf d => ?_, ?_, ?_, h⟩⟩
    · rw [Ideal.mem_comap] at hf ⊢
      rw [rename_base_homogeneousComponent]
      exact hW.multiHomog _ hf _
    · rw [← comap_mIdealOver_graph (S := k) x s]
      exact Ideal.comap_mono hle
    · obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
      have hXi : rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i : Kleiman.Poly k N) =
          X ⟨baseBlock, i⟩ := rename_X _ _
      exact ⟨i, by rw [Ideal.mem_comap, hXi]; exact hi⟩
  rw [hsub, FieldNumbers.CutRegular.relDim_eq_natCast_iff, hdim, Fintype.card_sum, Fintype.card_unit]
  generalize ringKrullDim (Kleiman.Poly k N ⧸
    W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) = D
  induction D using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add]
    exact iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)
  | coe t =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_inj,
      WithBot.coe_inj]
    induction t using ENat.recTopCoe with
    | top => exact iff_of_false (by rw [top_add]; exact ENat.top_ne_natCast _) (ENat.top_ne_natCast _)
    | coe t =>
      norm_cast
      omega

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

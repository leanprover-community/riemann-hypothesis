module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
public import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ArchimedeanBoundTotalConstantSize
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsCuspFormFourClausesExplicitConstantStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogCardComponentsLeOfRowsBoundStatement
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

private lemma etexnum_one_le_rd (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ I2.PT.rd E := by
  unfold I2.PT.rd
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs (NumberField.discr_ne_zero E)
  exact_mod_cast h

theorem etEx_deg_two : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → 1 ≤ q → Real.log q ≤ 70 * large₂.sc.L → ETEx h (WeightFamilies.PPv D large₂ 200000 2) (EtArch h (I2.th (E := D.host.E) q R0) (200000 * zBase large₂ ^ 2)) := by
  intro D T h large₂ hrows DF q R0 hrun hq lq
  have hP : WeightFamilies.PPv D large₂ 200000 2 = 200000 * zBase large₂ ^ 2 := by
    unfold WeightFamilies.PPv
    rw [Real.rpow_two]
  rw [hP]
  refine GlobalTheory.T.exists_cuspForm_four_clauses_explicitConstant D T h DF q R0 _ _ hrun (fun j hj => ?_) (by positivity)
  rw [min_self]
  have hN := GlobalTheory.T.log_card_components_le_of_rows_bound D T h large₂ hrows j hj T.σ₀ T.good_σ₀
  obtain ⟨hL, lr, lρ, lf, -, hf⟩ := hrows
  have hm := D.R.two_le_m
  have hk := D.R.f_le_k
  have hn : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hmr : D.R.m ≤ D.R.r := by
    unfold Ranks.r
    unfold Ranks.n at hn
    omega
  have hz : zBase large₂ = (I2.PT.f D.host.E : ℝ) * D.R.r * large₂.sc.L := by
    rw [hostSize_f]; rfl
  rw [hz] at hN ⊢
  exact (archimedeanBoundTotalConstant_size D.host.E D.R.r q D.R.m _ large₂.sc.L hL (by rw [hostSize_f]; omega) (by omega) (by omega) hmr hq
    (etexnum_one_le_rd _) lρ (by rw [hostSize_f]; exact lf) lr lq hN).2

end GlobalTheory.EtaAn

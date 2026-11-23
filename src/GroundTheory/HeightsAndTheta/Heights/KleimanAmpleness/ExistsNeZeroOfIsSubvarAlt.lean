module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem exists_ne_zero_of_isSubvar {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {d : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  change MvPolynomial.X i ∈ RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.coneMap F x)
  rw [RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem VeryAmpleNefPlusAmple.equiv (hBun : BundleOfDeg.Statement) (hNef : ModelNefEq.Statement)
    (hVA : ModelVeryAmpleEq.Statement) (hDim : ModelDimEq.Statement) :
    Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement := by
  constructor
  · intro hA d F _ K _ _ ι _ Ω _ _ y k₀ hmod hdim μ hnef t ht
    obtain ⟨i₀, -⟩ := hmod.1 k₀
    have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
    let e : ι k₀ ≃ Fin (Fintype.card (ι k₀) - 1 + 1) :=
      (Fintype.equivFin _).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
    obtain ⟨Q, hQ⟩ := hBun F K ι Ω y k₀ _ e hmod μ
    have hs := (hDim F K ι Ω y k₀ _ e hmod d).mpr hdim
    have hn := (hNef F K ι Ω y k₀ _ e hmod μ Q hQ).mpr hnef
    obtain ⟨p, m, hp, hm, hva⟩ := hA F d Ω _ _ Q hs hn t ht
    exact ⟨p, m, hp, hm, (hVA F K ι Ω y k₀ _ e hmod μ Q hQ p m hp).mp hva⟩
  · intro hB k _ d Ω _ _ N x M hs hnef t ht
    have hx := exists_ne_zero_of_isSubvar hs
    obtain ⟨n, hn⟩ := Generated.full.{0, 0} k Ω N x M
    obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
      (M.tensorProd (twistBundle k x n)) (hn n le_rfl)
    have hgen : IsGraphGen M n g := hg
    have hmod := GraphModel.full k N Ω x M n (r + 1) g hx hgen
    have hsec := twist_secs_eq_secOver M n g hgen
    have hdim := (hDim k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod d).mp hs
    have hnef' := (hNef k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec).mp hnef
    obtain ⟨a, m, ha, hm, hva⟩ := hB d k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock hmod hdim
      (graphDeg n) hnef' t ht
    exact ⟨a, m, ha, hm, (hVA k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec a m ha).mpr hva⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTer
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem twistMul_twist_twistSys {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a : ℕ) (m c : ℤ) :
    (twistMul M a m).twist (twistSys S x c) = twistMul M a (m + c) := by
  rw [twistMul, twistMul, SubSystem.twist_assoc, twistSys_twist_eq_add]

theorem ModelVeryAmpleEq.proof (hVA : VeryAmpleEq.Statement) (hMS : ModelMulSecs.Statement)
    (hCh : ModelChangeVeryAmple.Statement) : ModelVeryAmpleEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ a m _
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul Q a m
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (L.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen L n g := hg
  have hmod' := GraphModel.full F N Ω _ L n (r + 1) g hx hgen
  have hsec := twist_secs_eq_secOver L n g hgen
  have hH : ∀ c : ℤ, (L.twist (twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver F y (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro c
    rw [hL, twistMul_twist_twistSys, hMS F K ι Ω y k₀ N e hmod β Q hQ a (m + c), add_smul, add_assoc]
  rw [← hL, hVA F N Ω _ L n (r + 1) g hgen]
  exact hCh F Ω N (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock (Equiv.refl _) K ι y k₀ e hmod' hmod rfl
    (graphDeg n) (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (fun c => (hsec c).symm.trans (hH c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

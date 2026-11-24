module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
public import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Bad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
variable {Y : Spc F E n} {B : Base F E} {v : Pl F} {r s : ℕ}
theorem theta_pm_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) : Y.θ w = 1 ∨ Y.θ w = -1 :=
  cartan_pm (h.sig w) h0 (fun i j => (hB.cm.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j))) (h.cartan w)
theorem commute_theta_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) (w) (A) : Commute A (Y.θ w) := by
  rcases _root_.GlobalTheory.ThK.Dbl.Bad.theta_pm_k hB h h0 w with e | e <;> rw [e]
  exacts [Commute.one_right _, Commute.neg_one_right _]
theorem stab_iff_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (UA σ Y.J)} (hK : IsStab B K)
    {g : UA σ Y.J} : g ∈ K ↔ ∀ v, IntAt v g :=
  (hK g).trans ⟨fun a _ z hz _ => a.2 z hz, fun a => ⟨fun w => _root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _, fun _ hz =>
    ⟨mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).1) hz, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (a v z h1 h2).2) hz⟩⟩⟩
theorem emb_mem_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h : Y.IsHerm σ B r s) (h0 : min r s = 0) {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K)
    {e : UA σ Y.J × UA σ Y.J →* G2 σ Y} (he : ∀ g g', IsEmb g g' (e (g, g'))) {g : UA σ Y.J} (hg : ∀ v, IntAt v g) :
    e (g, 1) ∈ K := by
  refine (hK _).2 ⟨fun w => ?_, fun z z' hz hz' k hk => ?_⟩
  · rw [he g 1, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
    simp only [Commute, SemiconjBy, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).eq, (_root_.GlobalTheory.ThK.Dbl.Bad.commute_theta_k hB h h0 w _).neg_right.eq]
  · obtain ⟨g', e1, hg'⟩ : ∃ g', k = e (g', 1) ∧ mat g' *ᵥ z ∈ latHat Y := by
      rcases hk with rfl | rfl
      · exact ⟨g, rfl, mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).1) hz⟩
      · exact ⟨g⁻¹, by rw [← map_inv, Prod.inv_mk, inv_one], mulVec_mem h.lat.toIsLattice (fun v z h1 h2 => (hg v z h1 h2).2) hz⟩
    rw [e1, he g' 1, Matrix.fromBlocks_mulVec, show mat (1 : UA σ Y.J) = 1 from rfl]
    simpa using ⟨hg', hz'⟩
end GlobalTheory.ThK.Dbl.Bad
end
end

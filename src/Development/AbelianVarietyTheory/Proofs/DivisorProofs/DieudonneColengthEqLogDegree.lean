module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogenyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAddStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthCompositionStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny p k H G g hg
  have hpG := ((GlobalTheory.T.pDivisibleGroup_isogeny_basic_properties p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add p k G H G q g e e' _ he he' hpG
  have h1 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k G H q e hq' he
  have h2 := GlobalTheory.T.kernelDegree_le_dieudonneColength p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := GlobalTheory.T.witt_module_length_composition p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu

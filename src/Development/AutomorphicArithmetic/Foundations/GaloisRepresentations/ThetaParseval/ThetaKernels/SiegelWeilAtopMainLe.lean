module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem LD.n_succ_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : L.n + 1 = d.n := by
  have h1 : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    rw [Finset.mem_image, Finset.mem_erase]
    simp only [Finset.mem_univ, true_and, and_true]
    exact ((L.rng i).trans Set.mem_range).symm
  have h2 := congrArg Finset.card h1
  rw [Finset.card_image_of_injective _ L.inj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h2
  have := L.i₀.pos
  omega
theorem mainInequality_by_corank (hRD : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hEq : _root_.PositivityTheory.SiegelWeilFormula.MainEq_k) (hStep : _root_.PositivityTheory.SiegelWeilFormula.Step_k)
    (hVA : _root_.PositivityTheory.SiegelWeilFormula.VacAll_k) (k : ℕ) : ∀ d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ, d.m ≤ d.n → d.n - d.m = k → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d := by
  induction k with
  | zero =>
    intro d h hk
    exact hEq F E σ d (by omega)
  | succ k ih =>
    intro d h hk
    have hm := d.ok.hm
    obtain ⟨L⟩ := hLD F E σ d (by omega)
    have hL := _root_.PositivityTheory.SiegelWeilFormula.Atop.LD.n_succ_k L
    obtain ⟨R⟩ := hRD F E σ d
    obtain ⟨R'⟩ := hRD F E σ L.sd
    have hC' : _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 L.sd := ih L.sd (by show d.m ≤ L.n; omega) (by show L.n - d.m = k; omega)
    have hV' : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R' := fun Φ hΦ hv x => hC' Φ (hPK F E σ L.sd R' Φ hΦ ((hVK F E σ L.sd R').2.1 hv)) x
    exact hVA F E σ d R 2 (hStep F E σ d R L R' (by omega) hV')
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
theorem Atop.mainLeOf_k : _root_.PositivityTheory.SiegelWeilFormula.MainLeOf_k := by
  intro hRD hLD hVK hPK hEq hStep hVA F E _ _ _ _ _ σ d h
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.mainInequality_by_corank hRD hLD hVK hPK hEq hStep hVA _ d h rfl
end PositivityTheory.SiegelWeilFormula
end
end

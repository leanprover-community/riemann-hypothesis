module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem LD.n_succ {d : SD σ} (L : LD d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    Equiv.ofBijective (fun a => ⟨L.em a, (L.rng _).2 ⟨a, rfl⟩⟩)
      ⟨fun a b h => L.inj (congrArg Subtype.val h), fun i => by
        obtain ⟨a, ha⟩ := (L.rng i.1).1 i.2
        exact ⟨a, Subtype.ext ha⟩⟩
  have h := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h
  have := L.i₀.pos
  omega

theorem rank_difference_induction (hRD : RDEx) (hLD : LDEx) (hVK : VacK) (hPK : PolyKFin) (hEq : MainEq) (hStep : Step)
    (hVA : VacAll) (k : ℕ) : ∀ d : SD σ, d.m ≤ d.n → d.n - d.m = k → MainC 2 d := by
  have hCV : ∀ (d : SD σ) (R : RD d) (c : ℂ), MainC c d → MainV c R := by
    intro d R c hC Φ hΦ hv x
    exact hC Φ (hPK F E σ d R Φ hΦ ((hVK F E σ d R).2.1 hv)) x
  have key : ∀ k' : ℕ, ∀ d : SD σ, d.m ≤ d.n → d.n - d.m = k' → ∀ R : RD d, MainV 2 R := by
    intro k'
    induction k' with
    | zero =>
      intro d h1 h2 R
      exact hCV d R 2 (hEq F E σ d (by omega))
    | succ k' ih =>
      intro d h1 h2 R
      have hm := d.ok.hm
      obtain ⟨L⟩ := hLD F E σ d (by omega)
      obtain ⟨R'⟩ := hRD F E σ L.sd
      have hn := LD.n_succ L
      refine hStep F E σ d R L R' (by omega) (ih L.sd ?_ ?_ R')
      · show d.m ≤ L.n
        omega
      · show L.n - d.m = k'
        omega
  intro d h1 h2
  obtain ⟨R⟩ := hRD F E σ d
  exact hVA F E σ d R 2 (key k d h1 h2 R)

end PositivityTheory.SiegelWeilFormula.Atop

namespace PositivityTheory.SiegelWeilFormula

theorem Atop.mainLeOf : MainLeOf := by
  intro hRD hLD hVK hPK hEq hStep hVA F E _ _ _ _ _ σ d h
  exact Atop.rank_difference_induction hRD hLD hVK hPK hEq hStep hVA _ d h rfl

end PositivityTheory.SiegelWeilFormula

end

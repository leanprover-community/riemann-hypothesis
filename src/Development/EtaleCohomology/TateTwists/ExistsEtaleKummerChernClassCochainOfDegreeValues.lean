module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative, Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues

-- ===== clump member: Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleFirstChernKummerCocycleRep (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def first_chern_class_exists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ, IsEtaleFirstChernKummerCocycleRep q L γ

end LateralTheory.EtaleFoundations
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative =====

-- ===== clump member: Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues =====
-- clump-header: {"m": "Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues", "h": "module\n\npublic import Development.EtaleCohomology.TateTwists.FirstChernSpecOfRepresentative\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicGeometry.Modules.Sheaf\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleKummerChernClassCochainOfLineBundle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) α 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) α 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) α 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def ExistsEtaleKummerChernClassCochain : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α

def EtaleKummerChernClassCochainIsCocycle : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α → δ 2 3 α = 0

def EvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def ExistsNaturalEtaleKummerChernClassDegreeOneValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def ExistsNaturalEtaleKummerChernClassDegreeTwoValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

noncomputable def vals {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 2 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 0, _, _, _, _ => 0
  | Nat.succ 0, s, h, U, x => (show (1 : ℤ) = s by omega) ▸ a1 U x
  | Nat.succ (Nat.succ 0), s, h, U, x => (show (0 : ℤ) = s by omega) ▸ a2 U x
  | Nat.succ (Nat.succ (Nat.succ _)), _, _, _, _ => 0

theorem vals_nat {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a1 U x) = a1 V (x.res g))
    (h2 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a2 U x) = a2 V (x.res g)) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (vals a1 a2 p s h U x) = vals a1 a2 p s h V (x.res g) := by
  intro p
  match p with
  | 0 =>
    intro s h V U g x
    simp [vals]
  | Nat.succ 0 =>
    intro s h V U g x
    subst s
    exact h1 V U g x
  | Nat.succ (Nat.succ 0) =>
    intro s h V U g x
    subst s
    exact h2 V U g x
  | Nat.succ (Nat.succ (Nat.succ _)) =>
    intro s h V U g x
    simp [vals]

theorem exists_etale_kummer_chern_class_cochain_of_degree_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) : ExistsEtaleKummerChernClassCochain := by
  intro q _ E L hi
  obtain ⟨a1, n1, e1⟩ := h1 q L hi
  obtain ⟨a2, n2, e2⟩ := h2 q L hi
  obtain ⟨α, hα⟩ := hmk (ZMod q) (vals a1 a2) (vals_nat a1 a2 n1 n2)
  refine ⟨α, ?_, ?_, ?_⟩
  · intro U x; rw [hα]; rfl
  · intro U x v hv; rw [hα]; exact e1 U x v hv
  · intro U x v w hv hw; rw [hα]; exact e2 U x v w hv hw

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) (hd : EtaleKummerChernClassCochainIsCocycle) :
    LateralTheory.EtaleFoundations.first_chern_class_exists := by
  intro q _ E L hi
  obtain ⟨α, hα⟩ := exists_etale_kummer_chern_class_cochain_of_degree_values hmk h1 h2 q L hi
  exact ⟨Cocycle.mk α 3 (by norm_num) (hd q L hi α hα), hα⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues =====

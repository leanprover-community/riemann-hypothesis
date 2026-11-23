module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIso
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

theorem _root_.GlobalTheory.T.unique_cochain_on_disc_product : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ) (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n), (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c V (F.map g.op x) = (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) → ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)), (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) = c U x := by
  first | (exact @GlobalTheory.EtC.cochain_disc_glue) | (exact GlobalTheory.EtC.cochain_disc_glue) | (intros; apply GlobalTheory.EtC.cochain_disc_glue  <;> assumption)

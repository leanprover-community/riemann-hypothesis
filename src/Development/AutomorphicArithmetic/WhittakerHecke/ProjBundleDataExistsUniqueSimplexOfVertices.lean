module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
public import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataExistsSimplexOfRel
public import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataSimplexExtOfVertices
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

theorem UpperTheory.projBundleData_existsUnique_simplex_of_vertices :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx P.S 0 U),
        (∀ i j, (P.pS.app (op ⦋0⦌)).app (op U) (t i) = (P.pS.app (op ⦋0⦌)).app (op U) (t j)) →
        ∃! z : Sx P.S n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i := by
  intro T W r d P n U t h
  have hrel : ∀ i j, P.rel U (P.sv (t i) 0) (P.sv (t j) 0) := by
    intro i j
    have hq : (Quotient.mk (P.relS U) (P.sv (t i) 0)) = Quotient.mk (P.relS U) (P.sv (t j) 0) := h i j
    exact Quotient.exact hq
  obtain ⟨z, hz⟩ := UpperTheory.projBundleData_exists_simplex_of_rel P n U (fun i => P.sv (t i) 0) hrel
  have key : ∀ (y : Sx P.S n U) (i : Fin (n + 1)),
      P.sv (Sx.along y (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) 0 = P.sv y i := by
    intro y i
    rw [PBData.sv_along]
    simp
  refine ⟨z, fun i => ?_, fun z' hz' => ?_⟩
  · apply UpperTheory.projBundleData_simplex_ext_of_vertices P
    intro k
    have hk : k = 0 := Fin.fin_one_eq_zero k
    rw [hk, key, hz]
  · apply UpperTheory.projBundleData_simplex_ext_of_vertices P
    intro i
    rw [← key, hz' i, hz]

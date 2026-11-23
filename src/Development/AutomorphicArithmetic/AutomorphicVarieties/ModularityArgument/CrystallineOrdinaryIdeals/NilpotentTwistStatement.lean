module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
private theorem sh_s0_eq_diagonal_psi_sub_psi {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (b : Fin 3) : D.sh r b D.s0 = Matrix.diagonal (fun c => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ c D.s0) - algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ b D.s0)) := by
  rw [Dat3.sh, h, Matrix.scalar_apply, Matrix.diagonal_sub]
private theorem tr_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) (h : (r D.s0).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0))) (a : Fin 3) : D.tr r a = algebraMap O C (D.cc a) * (r D.fr).mat a a := by
  rw [Dat3.tr, sh_s0_eq_diagonal_psi_sub_psi D r h, sh_s0_eq_diagonal_psi_sub_psi D r h, Matrix.diagonal_mul_diagonal, Matrix.trace, Fin.sum_univ_three]
  simp only [Matrix.diag, Matrix.diagonal_mul, Dat3.cc, map_mul, map_sub]
  fin_cases a <;> simp <;> ring


theorem _root_.GlobalTheory.T.ordinary_derivative_entry_formula : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)), (r (GlobalTheory.OrdLoc.s0 D)).mat = Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (GlobalTheory.OrdLoc.s0 D))) → ∀ a : Fin 3, GlobalTheory.OrdLoc.dd D r a = algebraMap O C (GlobalTheory.OrdLoc.cc D a * GlobalTheory.OrdLoc.cc D (a + 1)) * ((r (GlobalTheory.OrdLoc.fr D)).mat a a - algebraMap O C ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) * (r (GlobalTheory.OrdLoc.fr D)).mat (a + 1) (a + 1)) := by
  intro l _ O _ _ _ D C _ _ r h a
  simp only [Dat3.dd, tr_lemma_2 D r h, map_mul]
  ring

module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

variable {l : ℕ} [Fact l.Prime]

private def coordPair (P : LocPrime l) (L : FinExt l) (a : ℕ) :
    (Fin a → ↥L.1) →+ Bst P →+ (Fin a → OB P) :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun b i => ((v i : ↥L.1) : Om l) ⊗ₜ[↥(MaximalUnramifiedExtension l)] b)
      (fun b b' => by funext i; simp [TensorProduct.tmul_add]))
    (fun v v' => by
      ext b i
      simp [TensorProduct.add_tmul])

theorem coordEx_holds : CoordEx := by
  intro l _ P L a
  refine ⟨TensorProduct.liftAddHom (coordPair P L a) ?_, ?_⟩
  · intro r v b
    funext i
    simp only [coordPair, AddMonoidHom.mk'_apply, Pi.smul_apply]
    rw [show ((r • v i : ↥L.1) : Om l) = r • ((v i : ↥L.1) : Om l) from rfl]
    exact TensorProduct.smul_tmul r _ b
  · intro v b i
    rfl

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end

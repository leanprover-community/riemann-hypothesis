module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison


theorem UpperTheory.Gal.crystallineComparison.detCoLift_of :
    CoFacts → WdLift → CoLift := by
  intro hco hwd l _ P ι K LL a ρ S _ _ π h1 h2
  obtain ⟨f1, f2, f3, -, -⟩ := hco ℚ_[l] ↥LL.1 (Bst P) a
  refine Exists.elim (hwd l P ι K LL (Fin a → ↥LL.1) ρ (Fin a → S)
    (fun x i => π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) ?_ ?_ ?_)
    fun j hj => ⟨j, fun x i => by rw [hj]⟩
  · intro x y
    funext i
    rw [Submodule.coe_add, f1, Pi.add_apply, Pi.add_apply, map_add (f := _)]
  · intro c x
    funext i
    change π (co (c • (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) = _
    rw [f2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, h1,
      Algebra.smul_def]
  · intro c x
    funext i
    have e : co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) = _ :=
      f3 (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)
    show π (co (mulV P ↥LL.1 (Fin a → ↥LL.1) c (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P)) i) =
      ι (c : Om l) • π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)
    rw [e, Pi.smul_apply, smul_eq_mul, RingHom.map_mul π, h2, Algebra.smul_def]

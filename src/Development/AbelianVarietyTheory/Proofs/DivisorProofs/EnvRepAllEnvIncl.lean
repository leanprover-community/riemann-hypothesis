module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}


open Classical in
def lieRep (R : RealPoints θ V) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (SmF θ V) :=
  DirectSum.toLieAlgebra _ (fun τ => (envRep R τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change (envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)) * envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) * envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(envRep_comm R h _ _).eq, sub_self]

def envRepAll (R : RealPoints θ V) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (SmF θ V) :=
  UniversalEnvelopingAlgebra.lift ℂ (lieRep R)


open Classical in
def envIncl (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] GlobalTheory.AutFinLit.Env V :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
    (DirectSum.lieAlgebraOf ℂ D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ))

open Classical in
theorem envIncl_ι (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x) =
      UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x) := by
  simp [envIncl]

theorem envRepAll_envIncl (R : RealPoints θ V) (τ : D.what₂.Tau) (u : EnvAt V τ) :
    envRepAll R (envIncl V τ u) = envRep R τ u := by
  classical
  have : (envRepAll R).comp (envIncl V τ) = envRep R τ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    change envRepAll R (envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x)) = envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [envIncl_ι, envRepAll, UniversalEnvelopingAlgebra.lift_ι_apply, lieRep]
    exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x
  exact congrArg (fun f : EnvAt V τ →ₐ[ℂ] _ => f u) this

end GlobalTheory.CentralOps

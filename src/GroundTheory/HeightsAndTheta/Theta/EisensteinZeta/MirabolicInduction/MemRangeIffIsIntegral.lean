module

public import Mathlib
public import GroundTheory.AutomorphicForms.HermitianSpaces
public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import GroundTheory.AutomorphicForms.HermitianWitt
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.HeightsAndTheta.Theta.CMDatum
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

namespace FunctionalEquationAlt

open NumberField TensorProduct Module GroundTheory.Automorphic
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CAt

variable {E : Type} [Field E] (σ : E →+* ℂ)

instance : Field (CAt σ) := inferInstanceAs (Field ℂ)

instance : Algebra ℂ (CAt σ) := inferInstanceAs (Algebra ℂ ℂ)

instance : Algebra E (CAt σ) := ((ofComplex σ).toRingHom.comp σ).toAlgebra

instance : SMulCommClass E ℂ (CAt σ) where
  smul_comm a c z := by
    rw [smul_def, complex_smul_def, complex_smul_def, smul_def, mul_left_comm]

end CAt

open CAt

section FibSMul

variable {E : Type} [Field E] (σ : E →+* ℂ) (V : Type) [AddCommGroup V] [Module E V]

instance (W : Type) [AddCommGroup W] [Module E W] :
    LinearMap.CompatibleSMul (Fib σ V) (Fib σ W) ℂ (CAt σ) where
  map_smul f c x := by
    rw [show c • x = (ofComplex σ c) • x from (fib_smul_eq σ V _ x).symm,
      show c • f x = (ofComplex σ c) • f x from (fib_smul_eq σ W _ (f x)).symm, map_smul]

instance [FiniteDimensional E V] : FiniteDimensional ℂ (Fib σ V) := by
  have : Module.Finite ℂ (CAt σ) := Module.Finite.equiv (ofComplex σ).toLinearEquiv
  exact Module.Finite.trans (CAt σ) (Fib σ V)

end FibSMul

attribute [instance] MetSpace.instAddCommGroup MetSpace.instModule MetSpace.instFD
  MetSpace.instModuleO MetSpace.instTower

variable {E : Type} [Field E] [NumberField E]

namespace MetSpace

variable (S : MetSpace E)

instance (τ : InfinitePlace E) : AddCommGroup (S.FibSp τ) :=
  inferInstanceAs (AddCommGroup (Fib τ.embedding S.V))

instance (τ : InfinitePlace E) : Module ℂ (S.FibSp τ) :=
  inferInstanceAs (Module ℂ (Fib τ.embedding S.V))

instance (τ : InfinitePlace E) : NormedAddCommGroup (S.FibSp τ) :=
  letI : InnerProductSpace.Core ℂ (S.FibSp τ) := S.form τ
  this.toNormedAddCommGroup

instance (τ : InfinitePlace E) : InnerProductSpace ℂ (S.FibSp τ) := InnerProductSpace.ofCore _

instance (τ : InfinitePlace E) : FiniteDimensional ℂ (S.FibSp τ) :=
  inferInstanceAs (FiniteDimensional ℂ (Fib τ.embedding S.V))

end MetSpace

namespace MetSpace

variable (S : MetSpace E)

end MetSpace

namespace MetSpace

variable (S : MetSpace E)

end MetSpace

section Lattices

variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

abbrev espan (A : Submodule (𝓞 E) V) : Submodule E V := Submodule.span E (A : Set V)

section Herm

variable {F : Type} [Field F] [Algebra F E] [Algebra.IsQuadraticExtension F E]

end Herm

end Lattices

namespace MetSpace

variable (S : MetSpace E)

end MetSpace

namespace MetSpace

variable (S : MetSpace E)

end MetSpace

namespace SelfDualFrame

variable {F : Type} [Field F] [Algebra F E] [Algebra.IsQuadraticExtension F E]

end SelfDualFrame

section Standard

variable (E) (n : ℕ)

variable {E n}

variable (E n)

variable {E n}

end Standard

section Frame

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]

variable {F}

end Frame

section Frame

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]

end Frame

section Frame2

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
  [Algebra F E] [Algebra.IsQuadraticExtension F E]

end Frame2

end

end FunctionalEquationAlt

end GroundTheory.Heights₂.Theta

module

public import Mathlib
public import GroundTheory.AutomorphicForms.FourierWhittaker
public import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
public import GroundTheory.LocalFields.LocalZeta
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import Formalism.RealPlaceAnalysis.StatementE

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3

section Mat

variable {R : Type*} [CommRing R]

end Mat

section Fin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def IsUnit1 (μ : Fˣ →* ℂˣ) : Prop := Continuous μ ∧ ∀ x, ‖((μ x : ℂˣ) : ℂ)‖ = 1

def IsStd (ψ : AddChar F Circle) : Prop := Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0

end Fin

def mulR : Measure ℝˣ := Measure.comap Units.val (volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹)

abbrev Pl : Type := HeightOneSpectrum (𝓞 ℚ)
abbrev Qv (v : Pl) : Type := v.adicCompletion ℚ

instance (v : Pl) : MeasurableSpace (Qv v) := borel _
instance (v : Pl) : BorelSpace (Qv v) := ⟨rfl⟩

open UpperHalfPlane CongruenceSubgroup in
open scoped MatrixGroups ModularForm in
structure IsForm (k N : ℕ) (χ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) (k : ℤ)) (a : ℕ → ℂ) : Prop where
  char : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → (f : ℍ → ℂ) ∣[(k : ℤ)] γ = χ ((γ 1 1 : ℤ) : ZMod N) • (f : ℍ → ℂ)
  exp : ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (f τ)

def IsEig (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧ ∀ p n : ℕ, p.Prime → a p * a n = a (p * n) + if p ∣ n then χ p * (p : ℂ) ^ (k - 1) * a (n / p) else 0

def pOf (v : Pl) : ℕ := Ideal.absNorm v.asIdeal

end Ad3

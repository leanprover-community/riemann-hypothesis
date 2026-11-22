module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoNOfKato
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base
open UpperTheory.V.Alg

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

namespace UpperTheory.V.Th

def BkOrd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TotallyDisconnectedSpace H] (φ : H →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ →
    ∀ (n : ℕ) (ρ : H →* GL (Fin n) (Qbar l)) (ψ : Fin n → H →* (Qbar l)ˣ) (m : Fin n → ℤ) (k : ℕ), Continuous ρ → W.HasFlag ρ ψ →
      StrictAnti m → 0 < k →
      (∀ i j g, φ g ∈ Loc.Iq l → (ψ i g / ψ j g * Loc.cycA l l (Qbar l) (φ g) ^ (m j - m i)) ^ k = 1) →
      (∃ g, Loc.cycA l l (Qbar l) (φ g) = 1 ∧ Pr.FreeRatios fun i => ψ i g) →
      ∀ y ∈ Loc.finiteCocycles φ (Loc.adGL ρ), OrdAt ((Loc.Iq l).comap φ) ρ ψ y

def AdDown : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K L : Type) [Field K] [NumberField K] [IsCMField K]
    [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω], Module.finrank ℚ K = 2 →
    galOf ℚ L Ω ≤ galOf ℚ K Ω → ∀ (s : W.HidaSetting l L Ω) (V : s.Lev) (n : ℕ) (r : G K Ω →* GL (Fin n) (Qbar l))
      (μ : G K Ω →* (Qbar l)ˣ) (R : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin n) (Fin n) (Qbar l))), Continuous r →
      Af.IsAdOf r μ R → ∀ (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (ka : G L Ω →* (Qbar l)ˣ),
      (∀ (g : G L Ω) (t : G K Ω), galEmb ℚ L Ω g = galEmb ℚ K Ω t → W.mat ρ (V.pr g) = (ka g : Qbar l) • W.mat r t) →
      (∀ (g g' : G L Ω) (t : G K Ω), W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ → galEmb ℚ L Ω g = galEmb ℚ K Ω t →
        ka g * ka g' * μ t = cycBar L Ω l g ^ (1 - (n : ℤ))) → AdZero V ρ → Af.BlochKatoSelmerVanishes l R

def AdZero2 {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [Fact l.Prime] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (η : G ℚ Ω →* ℤˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∀ θ : G ℚ Ω →* (Qbar l)ˣ, (∀ g, (θ g : Qbar l) = ((η g : ℤˣ) : ℤ)) →
    ∀ R : Representation (Qbar l) (G ℚ Ω) (Matrix (Fin 2) (Fin 2) (Qbar l)),
      Af.IsAdOf (W.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) (θ.comp (AlgEquiv.restrictScalarsHom ℚ)) R →
      Af.BlochKatoSelmerVanishes l R

end UpperTheory.V.Th

end

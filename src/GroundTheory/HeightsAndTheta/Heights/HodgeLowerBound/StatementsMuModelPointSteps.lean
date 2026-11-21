import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsHodgeFibrePt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.FlagLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

def IsHodgeFrame (D : ComponentDataHodge II Ψ K ι Ω E) (τ : Ψ) (b : Fin D.N → E τ) : Prop :=
  ∃ (c : (k : K) → ι k) (f : Ω), IsFrameOver D.y (D.W τ) c f b ∧
    Submodule.span Ω (b '' {i | (i : ℕ) < D.j}) = D.F τ


variable [DecidableEq Ψ] {D : ComponentDataHodge II Ψ K ι Ω E}

def muPointOf (P : PlueckerData D) (b : ∀ τ, Fin D.N → E τ) : (Σ k : MuBlocks D, ιMu P k) → Ω
  | ⟨Sum.inl k, i⟩ => D.y ⟨k, i⟩
  | ⟨Sum.inr (Sum.inl τ), m⟩ => P.gen τ (jIdx D) m (b τ ∘ Fin.castLE (jIdx D).isLt)
  | ⟨Sum.inr (Sum.inr τ), m⟩ => P.gen τ (lastIdx D) m (b τ ∘ Fin.castLE (lastIdx D).isLt)

def MuPointVanish.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (b : ∀ τ, Fin D.N → E τ), (∀ τ, IsHodgeFrame D τ (b τ)) →
    ∀ G ∈ mCoordIdeal (muPointOf P b), ∀ u ∈ muPts P, eval u (map (Int.castRingHom ℂ) G) = 0

def MuPointDense.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (b : ∀ τ, Fin D.N → E τ), (∀ τ, IsHodgeFrame D τ (b τ)) →
    PXmu P ≤ mCoordIdeal (muPointOf P b)


end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

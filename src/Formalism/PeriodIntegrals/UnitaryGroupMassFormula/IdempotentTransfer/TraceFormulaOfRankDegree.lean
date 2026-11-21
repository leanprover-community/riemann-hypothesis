import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice

noncomputable section

namespace PI.Dv.Tr

open PI.Dv

def RankPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      rkL A (cut A ρ (eps P * eG T) A.L) = rkT T P0 P A ρ

def DegPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      |degL A (cut A ρ (eps P * eG T) A.L) -
          ∑ s, (nS T P s : ℝ) * degL A (cut A ρ (eps P0 * eS T s) A.L)| ≤
        10 * laG G * (rkT T P0 P A ρ : ℝ)

def MuPart : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      (0 < rkT T P0 P A ρ →
        muMaxL A (cut A ρ (eps P * eG T) A.L) ≤ muMaxL A (cut A ρ (eps P0 * eG T) A.L) + 10 * laG G)


end PI.Dv.Tr

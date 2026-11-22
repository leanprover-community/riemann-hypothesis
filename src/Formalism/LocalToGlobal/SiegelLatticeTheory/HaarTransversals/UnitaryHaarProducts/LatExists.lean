module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDiff
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.FrameReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TameSurjectivity.RecUnram
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLand

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

end Formalism.L2.SG.Pf.LatEx

namespace Formalism.L2.SG.Pf.LatEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DdG (D : D7) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
    ¬ (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≤ P.asIdeal)

end Formalism.L2.SG.Pf.LatEx

namespace Formalism.L2.SG.Pf.LatEx

section Gen

open Formalism.L2.SG.Saturated

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

end Gen

end Formalism.L2.SG.Pf.LatEx

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

section Gen2

open Formalism.L2.SG.Saturated

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

end Gen2

end Formalism.L2.SG.Pf.LatEx

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

section GF

open Formalism.L2.SG.Saturated

end GF

end Formalism.L2.SG.Pf.LatEx

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

section HR

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end HR

end Formalism.L2.SG.Pf.LatEx

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.LatEx

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Gen3

end Formalism.L2.SG.Pf.LatEx

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.LatEx

section D7sec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ddG_of (hSD : LatEx.SplitDiff) : DdG D := by
  intro P hP
  have hg : ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    simp [gS]
  rw [hg] at hP
  have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rcases P.isPrime.mem_or_mem hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hk⟩ := hk
  have hsq := PI.TameSurjW.notMem_sq_of_split (D.host.g_prime k) (D.nd.g_split k) P hk
  exact hSD D.host.F D.host.E (D.host.g k) P.asIdeal (D.host.g_prime k) P.isMaximal hk hsq

end D7sec

end Formalism.L2.SG.Pf.LatEx

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.LatEx

section D7asm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

end D7asm

end Formalism.L2.SG.Pf.LatEx

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.LatEx

section D7main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

end D7main

end Formalism.L2.SG.Pf.LatEx

namespace Formalism.L2.SG.Pf

end Formalism.L2.SG.Pf

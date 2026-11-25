module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.FockGram.SymGramPosSemidef
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.SplitVacAlg

variable {D : D7}

def frameLat (V : HSp D) : Submodule (𝓞 D.host.E) V.V := Submodule.span (𝓞 D.host.E) (Set.range V.frame)

theorem frameLat_isLattice (V : HSp D) : Submodule.IsFullLattice D.host.E (frameLat V) := by
  refine Submodule.IsFullLattice.mk
    (toIsLattice := Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span (Set.finite_range _))) ?_
  rw [frameLat, Submodule.span_span_of_tower]
  exact V.frame.span_eq

theorem frameLat_unimod (V : HSp D) (hV : V.gram = 1) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (frameLat V) := by
  have key := (Formalism.E.hermDual (𝓞 D.host.E) D.host.E V.V (Fin V.rank) V.hT V.frame
    (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    (fun s => ⟨⟨star (s : D.host.E), s.2.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩)).2
    (1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) (fun i j => by
      have := congrFun (congrFun hV i) j
      simp only [HSpace.gram] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [h]) (by simp)
  exact key.2.2 (by simp)

def stdLatSp (V : HSp D) (hV : V.gram = 1) : HSp D :=
  { V with L0 := frameLat V, standardTuple_isLattice := (frameLat_isLattice V).toIsLattice, baseLattice_isUnimodular := frameLat_unimod V hV }

theorem mem_frameLattice_iff_integral_coords (V : HSp D) (hV : V.gram = 1) (y : Fin V.rank → D.host.E) :
    y ∈ L0c D (stdLatSp V hV) ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i := by
  change ∑ i, y i • V.frame i ∈ Submodule.span (𝓞 D.host.E) (Set.range V.frame) ↔ _
  rw [V.frame.mem_span_iff_repr_mem (𝓞 D.host.E), Module.Basis.repr_sum_self]
  rfl

end GlobalTheory.SplitVacAlg

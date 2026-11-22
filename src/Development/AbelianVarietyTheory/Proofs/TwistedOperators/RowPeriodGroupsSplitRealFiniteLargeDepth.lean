module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowGrpSplit

theorem grpAt_all {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) : GrpAt ch := by
  intro j hj
  have hj' := List.mem_range'_1.1 hj
  obtain ⟨hi, hf, hc, he, hu, hrest⟩ := GlobalTheory.AdelicSplit.adelic_split D (ch.G.V (.grid D.R.m j))
  have hV := ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, by omega⟩ (fun k hk => by
    simp only [Node.grid.injEq] at hk; omega)
  have hlat := congLev_open_compact (ch.G.V (.grid D.R.m j))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (𝔪 := ⊤) top_ne_bot
  have hR : IsClosed ((rowGrp ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) ∧ (∀ a ∈ GinfC _, ∀ b ∈ GfC _, a * b ∈ rowGrp ch.G j → a ∈ rowGrp ch.G j ∧ b ∈ rowGrp ch.G j) ∧
      (∀ μ : Measure (rowGrp ch.G j), μ.IsHaarMeasure → μ.IsInvInvariant) ∧
      ∀ μ : Measure ((rowGrp ch.G j).subgroupOf (GfC _)), μ.IsHaarMeasure → μ.IsInvInvariant := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · rw [show rowGrp ch.G j = _ from dif_pos h1]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).1
      exact ⟨GlobalTheory.jacGrp_isClosed D _ _ _ _, a, b, c⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      rw [show rowGrp ch.G j = _ from (dif_neg h1).trans (dif_pos h2)]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).2 _ _ _
      exact ⟨GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ _ _, a, b, c⟩
  exact
    { clA := hi
      clB := hf
      clR := hR.1
      comm := hc
      prod := he
      split := hR.2.1
      le := inf_le_left
      cpt := hlat.2
      opn := by
        have e : (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) :
            Set (GfC (ch.G.V (.grid D.R.m j)))) = Subtype.val ⁻¹'
            (((ch.G.levMax (.grid D.R.m j)).comap (Lev.finE _) : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) :
              Set (GA D (ch.G.V (.grid D.R.m j)))) := by
          ext x
          exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
        rw [e]
        exact hlat.1.preimage continuous_subtype_val
      uniR := hR.2.2.1
      uniRB := hR.2.2.2
      uniB := hu }

theorem grpAt_big : Big fun ch => GrpAt ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => grpAt_all ch⟩⟩

end GlobalTheory.RowGrpSplit

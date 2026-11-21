import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InputsJumpsAtMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsOfInputsAndJumps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG5OfLocalDuality
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG6OfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightParameterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrredOfCharpolyEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleJOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfOverTwo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriplesGood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFiniteTypesAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DutiesOfLarge

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusionG5_of_local_duality : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG5 D := by
  first | exact @GlobalTheory.LevelPlaces.local_conditions_at_level | exact GlobalTheory.LevelPlaces.local_conditions_at_level | (intros; apply GlobalTheory.LevelPlaces.local_conditions_at_level <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

noncomputable section

namespace GlobalTheory.CoreFacts

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DepthZeroWild →
    GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → Core D := by
  intro hP hc hd hw hs hF hT hE hL D I hJ
  have R : GlobalTheory.NRows.Rows D := GlobalTheory.T.rows_of_inputs_and_jumps hP hc hd hL D I hJ
  have at' : SumRepresentations.AdmAt D := I.admAt R.a R.b
  have p1 : SumRepresentations.Conclusion1 D := I.Conclusion1 (GlobalTheory.T.parts_give_dimension D) R.a R.b
  have g3 : AdmissibleThreePrime.LabelDegreeHypotheses D :=
    GlobalTheory.AdmTame.main D R.a.tie0 R.a.a2 R.a.a5 (GlobalTheory.TieLabAt.main hL D I.P).2.1
  have rb : ResidualIrreducibleRankR D :=
    Formalism.MainNotions.AdmissibleThreePrime.residual_irreducible_of_theorem_three_prime D ⟨R.a.tieLab, g3⟩ R.a.a5 (GlobalTheory.BrauerNesbittIrr.litBNIrr _) R.c.rho R.c.dz
  have adm : SumRepresentations.admitted D := ⟨at', (residualIrreducibility_forms_equivalent D).2 rb, I.isot⟩
  have ex : GlobalTheory.StringRepresentationDecomposition.RbEx D := GlobalTheory.T.residualRankPartExists_of_jointCondition D R.c.rho
  have g5 : SumRepresentations.ConclusionG5 D := GlobalTheory.T.conclusionG5_of_local_duality hF hT hE D adm ex
  have g6 : SumRepresentations.ConclusionG6 D := GlobalTheory.T.conclusionG6_of_admissible D adm ex
  have z : SumRepresentations.ConclusionZ D := (SumRepresentations.multiplicity_statement_iff_reduced D I.isot p1.2.2).2 (GlobalTheory.T.reduced_form_of_local_inputs hL D I R)
  have wt : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := GlobalTheory.T.weight_parameter hL D I.P
  have bl : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D := GlobalTheory.BlockCharInf.main D I.P.cf I.P.C I.P.tp I.P.chr
  have rm : ∀ i : D.nd.Loc, Nonempty (RowMod D I.P.rep (D.nd.j i)) := fun i => by
    have hj := D.nd.j_range i
    obtain ⟨Y, -⟩ := GlobalTheory.RowModCanon.main hc hd hL D I.P I.X I.agree ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i)
      (by simp only; omega)
    exact ⟨Y⟩
  exact
    { what₂ := R
      adm := adm
      Conclusion1 := p1
      Conclusion2 := ⟨g5, g6, z⟩
      rhoBar := rb
      g3p := g3
      weight := wt
      block := bl
      g2 := GlobalTheory.T.admG2_pair_of_admissible D R.a.tie0 I.adm1 R.a.a2 R.a.a5
      admJ := fun L h => GlobalTheory.T.admissible_J_of_params D L R.a.tie0 I.adm1 R.a.a2 R.a.a5 wt bl h
      muUnr := GlobalTheory.MuUnrTie.main hP.fin hL D I.P
      depthG := GlobalTheory.T.depth_zero_of_localLanglands hP hw hs hL D I.P rm
      bc := I.bc
      lam := I.lam }

end GlobalTheory.CoreFacts

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_conclusion_of_inputs : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → Core D := by
  atlas_forward_decl GlobalTheory.CoreFacts.main
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NFacts.AtMemFacts

theorem oneField_of_nAt {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : Formalism.L2.Host.CharFrame D} {C : NChoice D} {tp : Formalism.L2.Host.TupTied D cf C}
    (a : NAt hL D cf C tp) : GlobalTheory.HeightCounting.SameTw.OneField D C := by
  have key : ∀ X : Σ (D₁ : D7) (c₁ : Formalism.L2.Host.CharFrame D₁) (C₁ : NChoice D₁), Formalism.L2.Host.TupTied D₁ c₁ C₁,
      X = ⟨withLoc a.nt.L, cfL a.nt.L a.nt.cf, chL a.nt.L a.nt.C, tpL a.nt.L a.nt.tp⟩ →
        GlobalTheory.HeightCounting.SameTw.OneField X.1 X.2.2.1 := by
    rintro _ rfl
    exact (GlobalTheory.HeightCounting.SameTw.oneField_withLoc a.nt.L a.nt.C).2 a.nt.Sp.tw_reads
  exact key _ a.nt.pack

theorem facts_atMem : PrN → GlobalTheory.NRows.HypothesesX → SerN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness →
    LocalTateDuality → LocalEulerChar → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => Facts (w.D Z) nch := by
  intro prn prx ser dzw dzs lf ltd lec hL
  have hA := GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.NRows.AtLayer.inputs_jumps_atMem prn prx hL)
    (GlobalTheory.HeightCounting.Up.TripFin.triplesGood prn ser hL)) (GlobalTheory.T.good_finite_types_all prn hL)
  refine EvG.imp hA fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hne hrx cp => ?_
  obtain ⟨⟨⟨I, -, jumps⟩, trip⟩, good⟩ := H kp w Z Wt p0 t nch n xd c hne hrx cp
  obtain ⟨ne⟩ := hne
  have core : Core (w.D Z) := GlobalTheory.T.full_conclusion_of_inputs prn.what₂ prn.hc prn.decay dzw dzs lf ltd lec hL (w.D Z) I jumps
  have large : GlobalTheory.CoefDuty.Large (w.D Z) := ne.large
  exact { core with
    c2 := GlobalTheory.LocCoincide.main hL (w.D Z) I.P.M c.a.nt.toNBuilt I.P.H.hecke
    large := large
    duties := GlobalTheory.CoefDuty.duties_of_large prn.cheb (w.D Z) large core.Conclusion1.1 core.rhoBar
    nct := n.tie
    trip := trip
    same := GlobalTheory.HeightCounting.SameTw.sameTwist_at hL (w.D Z) _ nch _ c.a (oneField_of_nAt c.a)
    good := good }

end GlobalTheory.NFacts.AtMemFacts

end
end

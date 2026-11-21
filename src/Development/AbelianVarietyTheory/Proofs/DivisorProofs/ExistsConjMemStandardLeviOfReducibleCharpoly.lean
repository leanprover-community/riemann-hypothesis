import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleUnitaryDataOfRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitFactorRegularSemisimpleReducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIdempotentOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIdempotentGivesDualStableSubspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualBasesIsotropicSubspacesDuality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCarryHyperbolicFamilyWittFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemStandardLeviWittFrame

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

namespace GlobalTheory.ConjLevi

theorem exists_conj_mem_levi : ∀ {D : D7} {V : HSp D}, 0 < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (Φ : WittFrame V) (γ : GF V), IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly → ¬ IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsPar P ∧ P.Nonempty ∧ rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  intro D V hr hRS Φ γ hss hirr hnf
  have hreg := GlobalTheory.T.isRegularSemisimpleUnitaryData_of_regular γ hss
  obtain ⟨hA, hP, -, hR, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨k, K, hK1, hK2, he, i, hi⟩ := GlobalTheory.T.exists_split_factor_regularSemisimple_reducible D.sp.cm.sig V.gram γ.1 hr hss hA hR hirr hnf
  obtain ⟨ε, hεL, hεε, hε0, hεi⟩ :=
    @GlobalTheory.T.exists_isotropic_idempotent_of_split_factor _ _ _ _ _ _ _ D.sp.cm.sig V.gram γ.1 hreg hA hP k K hK1 hK2 he i hi
  obtain ⟨X, X', hX0, hXi, hX'i, hXs, hX's, hn1, hn2⟩ := GlobalTheory.T.isotropicIdempotent_gives_dual_stable_subspaces γ ε hεL hεε hε0 hεi
  obtain ⟨a, x, x', ha0, ha, hx, hx', hli, hee, hff, hef⟩ := GlobalTheory.T.exists_dual_bases_isotropic_subspaces_duality X X' hX0 hXi hX'i hn1 hn2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitary_carry_hyperbolicFamily_wittFrame Φ ha x x' hli hee hff hef
  refine ⟨g, {stdVec ⟨a - 1, by omega⟩}, ?_, Finset.singleton_nonempty _, ?_⟩
  · have := isPar_stdPar ({⟨a - 1, by omega⟩} : Finset (Fin (wittIndex V)))
    simpa [stdPar] using this
  · exact GlobalTheory.T.conj_mem_standardLevi_wittFrame Φ γ g ha ⟨a - 1, by omega⟩ (by simp only; omega) x x' (fun i => (hg i).1)
      (fun i => (hg i).2) (by rw [hx]; exact hXs) (by rw [hx']; exact hX's)

end GlobalTheory.ConjLevi
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly : ∀ {D : D7} {V : HSp D}, 0 < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (Φ : WittFrame V) (γ : GF V), IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly → ¬ IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsPar P ∧ P.Nonempty ∧ rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  atlas_forward_decl GlobalTheory.ConjLevi.exists_conj_mem_levi

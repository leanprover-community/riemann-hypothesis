module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStdBlocksEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetDict

theorem twKer_one_eq_coinvariantsKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) :
    twKer ρ U 1 = Representation.Coinvariants.ker (ρ.comp U.subtype) := by
  unfold GlobalTheory.PRep.twKer Representation.Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨n, v, rfl⟩
    exact ⟨(n, v), by simp⟩
  · rintro ⟨⟨n, v⟩, rfl⟩
    exact ⟨n, v, by simp⟩

end GlobalTheory.CompanionTheory.JacquetDict

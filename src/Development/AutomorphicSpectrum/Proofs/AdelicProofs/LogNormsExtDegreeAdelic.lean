import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.WeilBound.CoreStatements.SesquilinearFractions.NBasic
import BuildAid.ForwardExisting

section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem logNorms_ext_deg_isAdelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) :=
  @PositivityTheory.Xgf.logNorms_ext_degree_adelic

end GlobalTheory.CompanionTheory.Ar.Fl
end

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic

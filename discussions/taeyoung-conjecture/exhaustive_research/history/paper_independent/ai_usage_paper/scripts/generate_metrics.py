"""Generate quantitative macros and the measurement table for the case study."""

from __future__ import annotations

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve()
PROJECT = HERE.parents[4]
OUT = HERE.parent.parent / "generated"
SURVEY = PROJECT / "history" / "paper_independent" / "survey_counts.py"


def load_survey_module():
    spec = importlib.util.spec_from_file_location("survey_counts", SURVEY)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def integer(value: int) -> str:
    return f"{value:,}"


def main() -> None:
    survey = load_survey_module()
    catalogue = survey.catalogue_counts()
    sessions = survey.session_counts()
    verification = survey.verification_counts()
    documents = survey.documentary_counts()
    git = survey.git_counts()

    workstation = sessions["workstation"]
    second = sessions["second_device"]
    chatgpt = sessions["chatgpt_export"]
    approval_total = workstation["approval_reviews"] + second["approval_reviews"]

    values = {
        "CatalogueRows": catalogue["rows"],
        "PositiveRows": catalogue["statuses"]["Positive"],
        "NegativeRows": catalogue["statuses"]["Negative"],
        "DirectCertificateRows": len(catalogue["direct_certificate_positive_rows"]),
        "PureChordalRows": len(catalogue["pure_chordal_positive_rows"]),
        "FailedRoutes": documents["failed_attempt_entries"],
        "ProofNotes": documents["tracked_tex_notes"],
        "CorrespondenceNotes": documents["notes_with_lean_correspondence_section"],
        "TypedPrompts": workstation["typed_prompts"],
        "GoalObjectives": workstation["goal_objectives"],
        "WorkstationCodexTurns": workstation["codex_worker_turns"],
        "WorkstationCodexTokens": workstation["codex_tokens_processed"],
        "WorkstationCodexCached": workstation["codex_cached_input_tokens"],
        "SecondPrimaryTurns": second["primary_live_turns"],
        "SecondCodexTokens": second["primary_tokens_processed"],
        "UltraTurns": second["live_ultra_turns"],
        "UltraHours": f"{second['live_ultra_turn_hours']:.2f}",
        "ClaudeInputTokens": workstation["claude_input_including_cache"],
        "ClaudeOutputTokens": workstation["claude_output_tokens"],
        "ChatGPTCampaignConversations": chatgpt["campaign_conversations"],
        "ChatGPTSatelliteConversations": chatgpt["satellite_conversations"],
        "ApprovalReviews": approval_total,
        "CampaignCommits": git["campaign_commits_through_final_classification"],
        "ClaudeTrailerCommits": git["commits_with_claude_coauthor_trailer"],
        "BoundedRuns": verification["bounded_row_runs"],
        "BoundedHours": f"{verification['total_hours']:.2f}",
        "BoundedPeakGiB": f"{verification['peak_gib']:.2f}",
        "AtlasFortyThreeModules": verification["atlas43_separate_chain"]["modules"],
        "AtlasFortyThreeHours": f"{verification['atlas43_separate_chain']['hours']:.1f}",
        "AtlasFortyThreePeakGiB": f"{verification['atlas43_separate_chain']['peak_gib']:.1f}",
    }

    OUT.mkdir(parents=True, exist_ok=True)
    macro_lines = [
        rf"\newcommand{{\{name}}}{{{integer(value) if isinstance(value, int) else value}}}"
        for name, value in values.items()
    ]
    (OUT / "metrics_macros.tex").write_text(
        "\n".join(macro_lines) + "\n", encoding="utf-8"
    )

    rows = [
        ("Human prompts in the workstation appendix", values["TypedPrompts"], "typed prompts to Codex or Claude Code"),
        ("Codex goal objectives", values["GoalObjectives"], "goal-interface objectives"),
        ("Workstation Codex worker turns", values["WorkstationCodexTurns"], "all extracted Codex worker turns"),
        ("Second-device primary live turns", values["SecondPrimaryTurns"], "non-replayed primary Codex turns"),
        ("Workstation Codex processed tokens", values["WorkstationCodexTokens"], "provider counter; includes cache traffic"),
        ("Second-device Codex processed tokens", values["SecondCodexTokens"], "provider counter; primary threads"),
        ("Claude Code input tokens", values["ClaudeInputTokens"], "input plus cache read and cache creation"),
        ("Claude Code output tokens", values["ClaudeOutputTokens"], "surviving workstation sessions"),
        ("ChatGPT Pro conversations", values["ChatGPTCampaignConversations"] + values["ChatGPTSatelliteConversations"], "campaign plus satellite conversations"),
        ("Automatic approval reviews", values["ApprovalReviews"], "29 workstation plus 16 second-device requests"),
        ("Numbered failed routes", values["FailedRoutes"], "entries in the failure ledger"),
        ("Bounded sequential row builds", values["BoundedRuns"], f"{values['BoundedHours']} h combined; peak {values['BoundedPeakGiB']} GiB"),
        ("Atlas 43 sequential chain", values["AtlasFortyThreeModules"], f"{values['AtlasFortyThreeHours']} h; peak {values['AtlasFortyThreePeakGiB']} GiB"),
    ]
    table = [
        r"\begin{table}[t]",
        r"\centering",
        r"\small",
        r"\caption{Observable campaign quantities.  Token counters retain each provider's semantics and are not added across providers.}",
        r"\label{tab:campaign-quantities}",
        r"\begin{tabular}{p{5.5cm} r p{6.0cm}}",
        r"\toprule",
        r"quantity & value & definition\\",
        r"\midrule",
    ]
    for label, value, definition in rows:
        rendered = integer(value) if isinstance(value, int) else str(value)
        table.append(f"{label} & {rendered} & {definition}\\\\")
    table.extend([r"\bottomrule", r"\end{tabular}", r"\end{table}", ""])
    (OUT / "metrics_table.tex").write_text("\n".join(table), encoding="utf-8")

    print("generated methodology metrics")


if __name__ == "__main__":
    main()

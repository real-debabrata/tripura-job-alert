# Tripura Job Alert

Personal-use job alert system for Tripura (Govt + Non-Govt).
For one person only. No accounts, no ads, no tracking.

## Status
Step 1 of 5: project skeleton. Scraper, app and alerts are coming.

## How it works
- A Python scraper runs on GitHub Actions (free) on a schedule.
- It writes `data/jobs.json`, `data/health.json`, `data/state.json`.
- A PWA (this website) reads those files. Your personal profile is stored ONLY on your phone.
- Alerts are sent through ntfy to a private topic stored in GitHub Secrets.

## Privacy rules
- This repo is PUBLIC. Put job data only here. Never put personal details, phone numbers or secrets in any file.
- Real secrets go only in GitHub > Settings > Secrets and variables > Actions.

## Full setup, testing and troubleshooting guide
Coming in the final step.

# Zoca Churn Dashboard

Auto-regenerated daily at 4:35 PM local time.

Live URL: https://siranjt.github.io/zoca-churn-dashboard/

**Churn rule:** a customer is counted only if they hold zero active-level
subscriptions (active / non_renewing / in_trial / future / paused) at the
customer level in Chargebee. Candidates come from the Metabase BaseSheet
(`churn_date` within the last 95 days) and are re-validated against Chargebee
on every run.

Data sources:
- Metabase BaseSheet
- Chargebee API
- Metabase communication CSVs (app chat, email, phone, video, SMS)

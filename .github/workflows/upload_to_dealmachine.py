import csv
import requests
import os

# Configuration
API_KEY = os.getenv('DEALMACHINE_API_KEY')
CSV_FILE = 'leads.csv' # Ensure this matches your generated filename
URL = "https://api.dealmachine.com/public/v1/leads"

def upload_leads():
    with open(CSV_FILE, mode='r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for row in reader:
            # Map your CSV headers to DealMachine fields
            payload = {
                "address": row['Address'],
                "city": row['City'],
                "state": row['State'],
                "zip": row['Zip'],
                "skip_trace": True  # Set to True to trigger auto-skiptrace
            }
            
            headers = {
                "Content-Type": "application/json",
                "x-api-key": API_KEY
            }

            response = requests.post(URL, json=payload, headers=headers)
            
            if response.status_code == 200:
                print(f"Successfully uploaded: {row['Address']}")
            else:
                print(f"Failed {row['Address']}: {response.text}")

if __name__ == "__main__":
    upload_leads()

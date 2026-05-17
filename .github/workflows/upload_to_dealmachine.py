import csv
import requests
import os
import time

# Configuration
API_KEY = os.getenv('DEALMACHINE_API_KEY')
CSV_FILE = 'leads.csv' 
URL = "https://api.dealmachine.com/public/v1/leads"

def upload_leads():
    if not os.path.exists(CSV_FILE):
        print(f"Error: {CSV_FILE} not found.")
        return

    with open(CSV_FILE, mode='r', encoding='utf-8') as f:
        # Using DictReader to access data via your specific headers
        reader = csv.DictReader(f)
        
        for row in reader:
            # Map your exact headers to DealMachine's API fields
            payload = {
                "address": row['Property Address'],
                "city": row['Property City'],
                "state": row['Property State'],
                "zip": row['Property Zip'],
                "skip_trace": True  # This triggers the skip trace automatically
            }
            
            headers = {
                "Content-Type": "application/json",
                "x-api-key": API_KEY
            }

            try:
                response = requests.post(URL, json=payload, headers=headers)
                
                if response.status_code in [200, 201]:
                    print(f"Success: {row['Property Address']}")
                else:
                    print(f"Failed {row['Property Address']}: {response.status_code} - {response.text}")
            
            except Exception as e:
                print(f"Connection error for {row['Property Address']}: {e}")

            # Short pause to respect API rate limits
            time.sleep(0.5)

if __name__ == "__main__":
    upload_leads()

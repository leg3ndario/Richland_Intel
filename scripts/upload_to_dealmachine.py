import csv
import requests
import os
import time

# Configuration
API_KEY = os.getenv('DEALMACHINE_API_KEY')
CSV_FILE = 'data/leads_ghl_export.csv' 
URL = "https://api.dealmachine.com/public/v1/leads/"

def upload_leads():
    if not os.path.exists(CSV_FILE):
        print(f"Error: {CSV_FILE} not found.")
        return

    # Check if API_KEY is actually being pulled from secrets
    if not API_KEY:
        print("Error: DEALMACHINE_API_KEY environment variable is not set.")
        return

    with open(CSV_FILE, mode='r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        
        for row in reader:
            addr = row['Property Address'].strip()
            city = row['Property City'].strip()
            state = row['Property State'].strip()
            zip_code = row['Property Zip'].strip()
            
            # Using the "Parsed Address" option from their docs
            payload = {
                "address": addr,
                "address2": "",
                "city": city,
                "state": state,
                "zip": zip_code,
                "skip_trace": True
            }
            
            # THE FIX: Standard Bearer Token Authorization
            headers = {
                "Authorization": f"Bearer {API_KEY}",
                "Content-Type": "application/json",
                "Accept": "application/json"
            }

            try:
                # Switching back to json=payload for the Bearer API
                response = requests.post(URL, json=payload, headers=headers)
                
                if response.status_code in [200, 201]:
                    json_response = response.json()
                    print(f"Success: {addr} | Response: {json_response}")
                elif response.status_code == 401:
                    print(f"Failed: 401 Unauthorized. Double-check your API Key in GitHub Secrets.")
                    break # Stop the loop if the key is invalid
                else:
                    print(f"Failed {addr}: {response.status_code} - {response.text}")
            
            except Exception as e:
                print(f"Error processing {addr}: {str(e)}")

            time.sleep(0.5)

if __name__ == "__main__":
    upload_leads()

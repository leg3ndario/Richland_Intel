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

    with open(CSV_FILE, mode='r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        
        for row in reader:
            # Match the documentation's address logic
            # Use .strip() to ensure no leading/trailing spaces mess with the geocoder
            addr = row['Property Address'].strip()
            city = row['Property City'].strip()
            state = row['Property State'].strip()
            zip_code = row['Property Zip'].strip()
            full_addr = f"{addr}, {city}, {state} {zip_code}"
            
            # Using 'data=' instead of 'json=' to send as Form Data
            payload = {
                "address": addr,
                "address2": "",
                "city": city,
                "state": state,
                "zip": zip_code,
                "full_address": full_addr,
                "skip_trace": "1" # Some Form APIs prefer "1" for true
            }
            
            headers = {
                "x-api-key": API_KEY
                # Note: 'requests' sets the correct Content-Type automatically for Form data
            }

            try:
                # We use data=payload for Form Data
                response = requests.post(URL, data=payload, headers=headers)
                json_response = response.json()
                
                if response.status_code in [200, 201]:
                    # The API likely returns a dictionary with 'data'
                    # Let's print the whole response briefly to be sure
                    print(f"Success: {addr} | Response: {json_response}")
                else:
                    print(f"Failed {addr}: {response.status_code} - {response.text}")
            
            except Exception as e:
                print(f"Error processing {addr}: {str(e)}")

            # Short pause to respect rate limits
            time.sleep(0.5)

if __name__ == "__main__":
    upload_leads()

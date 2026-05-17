import csv
import requests
import os
import time
import re

# Configuration
API_KEY = os.getenv('DEALMACHINE_API_KEY')
CSV_FILE = 'data/leads_ghl_export.csv' 
URL = "https://api.dealmachine.com/public/v1/leads/"
LIST_ID = 1254885 

def is_valid_address(addr):
    if not addr or len(addr) < 5:
        return False
    addr_up = addr.upper()
    junk_phrases = ['ANY HEIRS', 'SUMMONS', 'NOTICE', 'ESTATE OF', 'ORDER', 'THE PERSONAL', 'COMMONWEALTH', 'DECEASED']
    if any(phrase in addr_up for phrase in junk_phrases):
        return False
    if not addr[0].isdigit():
        return False
    if len(addr) > 120: # Paragraph protection
        return False
    return True

def clean_address(addr):
    # Remove ZIP debris like (29204)
    addr = re.sub(r'\(.*?\)', '', addr)
    # Handle "Unit" or "Ste" - DealMachine sometimes prefers these removed or clean
    addr = re.sub(r'\bUNIT\b', '#', addr, flags=re.IGNORECASE)
    return addr.strip().strip(',')

def upload_leads():
    if not os.path.exists(CSV_FILE):
        print(f"Error: {CSV_FILE} not found.")
        return

    with open(CSV_FILE, mode='r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        uploaded_count = 0
        skipped_count = 0
        
        for row in reader:
            raw_addr = row.get('Property Address', '').strip()
            if not is_valid_address(raw_addr):
                continue

            addr = clean_address(raw_addr)
            city = row.get('Property City', 'Columbia').strip()
            state = row.get('Property State', 'SC').strip()
            zip_code = row.get('Property Zip', '').strip()
            full_addr = f"{addr}, {city}, SC {zip_code}"
            
            payload = {
                "address": addr,
                "city": city,
                "state": "SC",
                "zip": zip_code,
                "full_address": full_addr, # Added for better matching
                "skip_trace": True,
                "lists": [LIST_ID]         # Changed to array format
            }
            
            headers = {
                "Authorization": f"Bearer {API_KEY}",
                "Content-Type": "application/json"
            }

            try:
                response = requests.post(URL, json=payload, headers=headers)
                res_data = response.json()
                
                # REVEAL THE TRUTH: Check if 'data' actually contains a lead object
                lead_data = res_data.get('data')
                # Sometimes it's a list, sometimes a dict
                if isinstance(lead_data, list):
                    has_id = len(lead_data) > 0
                else:
                    has_id = lead_data is not None and lead_data.get('id') is not None

                error_msg = ""
                if isinstance(res_data.get('error'), dict):
                    error_msg = res_data['error'].get('message', '')
                elif res_data.get('error'):
                    error_msg = str(res_data.get('error'))

                if response.status_code in [200, 201] and has_id:
                    print(f"✅ Added: {addr}")
                    uploaded_count += 1
                elif "already added" in error_msg.lower():
                    print(f"➖ Skipped: {addr} (Already in DM)")
                    skipped_count += 1
                else:
                    # This will now correctly catch the "Property not found" cases
                    print(f"❌ Failed: {addr} | Error: {error_msg if error_msg else 'Address Verification Failed'}")
                    skipped_count += 1
            
            except Exception as e:
                print(f"⚠️ Error processing {addr}: {str(e)}")

            time.sleep(0.4)

    print(f"\n--- SYNC COMPLETE ---")
    print(f"Successfully Added: {uploaded_count}")
    print(f"Failed/Skipped: {skipped_count}")

if __name__ == "__main__":
    upload_leads()
